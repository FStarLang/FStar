(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Custard.Mono

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Syntax.Syntax

module Free  = FStarC.Syntax.Free
module Ident = FStarC.Ident
module PC    = FStarC.Parser.Const
module S     = FStarC.Syntax.Syntax
module SS    = FStarC.Syntax.Subst
module TcEnv = FStarC.TypeChecker.Env
module TcUtil = FStarC.TypeChecker.Util
module U     = FStarC.Syntax.Util

let bclass_to_string (c:bclass) : string =
  match c with
  | Mono -> "Mono"
  | Poly -> "Poly"
  | Dropped -> "Dropped"

instance showable_bclass : showable bclass = { show = bclass_to_string }

(* Rule 2, first half: [{| c |}] desugars to an implicit binder whose qualifier
   is [Meta tcresolve]. *)
let is_tcresolve_binder (b:binder) : ML bool =
  match b.binder_qual with
  | Some (Meta t) ->
    (* The tactic term may have been eta-expanded or applied, so look at the
       head. *)
    let hd, _ = U.head_and_args_full t in
    U.is_fvar PC.tcresolve_lid hd
  | _ -> false

(* Rule 2, second half: a dictionary passed explicitly rather than through
   [{| |}] still has a class type. *)
let is_tcclass_binder (env:TcEnv.env) (b:binder) : ML bool =
  let hd, _ = U.head_and_args_full (U.unrefine (SS.compress b.binder_bv.sort)) in
  match (U.un_uinst hd).n with
  | Tm_fvar fv -> TcEnv.fv_has_attr env fv PC.tcclass_lid
  | _ -> false

let is_type_binder (b:binder) : ML bool =
  match (SS.compress (U.unrefine b.binder_bv.sort)).n with
  | Tm_type _ -> true
  | _ -> false

(* Rule 1: a non-informative binder carries no runtime value, so it is deleted
   rather than passed.  [unit] is deliberately excluded: dropping a unit binder
   would turn an impure function into a value, which changes when its effects
   run.  Removing unit thunks safely needs the purity discipline of section 7
   and is left to a later milestone. *)
let is_dropped_binder (env:TcEnv.env) (b:binder) : ML bool =
  let sort = b.binder_bv.sort in
  not (U.is_unit sort) &&
  not (is_type_binder b) &&
  TcUtil.must_erase_for_extraction env sort

let is_erased_binder (env:TcEnv.env) (b:binder) : ML bool =
  is_type_binder b || is_dropped_binder env b

(* Deleting *every* binder of an impure definition would turn it into a value,
   and its effects would then run at module initialization instead of when it
   is called.  So the last binder stays, carrying no information but keeping
   the definition a function.  Both the signature and the call sites derive
   their filtering from the same F* type, so they agree without communicating. *)
let keep_one_if_impure (env:TcEnv.env) (c:comp) (flags:list bool) : ML (list bool) =
  if Cons? flags && List.for_all (fun b -> b) flags && not (U.is_pure_or_ghost_comp c)
  then (match List.rev flags with
        | _ :: rest -> List.rev (false :: rest)
        | [] -> flags)
  else flags

let erased_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, c = U.arrow_formals_comp t in
  keep_one_if_impure env c (bs |> List.map (is_erased_binder env))

let type_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.map is_type_binder

let classify (env:TcEnv.env) (attrs:list attribute) (t:typ) : ML (list bclass) =
  let bs, comp = U.arrow_formals_comp t in
  let all_mono = U.has_attribute attrs PC.monomorphize_attr in
  let mono_types = Options.custard_monomorphize_types () in
  let init (b:binder) : ML bclass =
    if is_dropped_binder env b                                    (* rule 1 *)
    then Dropped
    else if all_mono                                                   (* rule 3 *)
    || U.has_attribute b.binder_attrs PC.monomorphize_attr        (* rule 3 *)
    || is_tcresolve_binder b                                      (* rule 2 *)
    || is_tcclass_binder env b                                    (* rule 2 *)
    || (mono_types && is_type_binder b)                           (* rule 4 *)
    then Mono
    else Poly
  in
  let cs = List.map init bs in
  (* Rule 5: if [b_j] is Mono and [b_i] is free in [b_j]'s type, [b_i] becomes
     Mono too.  Iterate to a fixpoint; the set only grows and is bounded by the
     number of binders, so at most [n] passes are needed. *)
  let bcs = List.zip bs cs in
  let pass (bcs:list (binder & bclass)) : ML (bool & list (binder & bclass)) =
    let needed =
      bcs |> List.collect (fun (b, c) ->
        match c with
        | Mono -> elems (Free.names b.binder_bv.sort)
        | _ -> [])
    in
    let changed = mk_ref false in
    let bcs = bcs |> List.map (fun (b, c) ->
      match c with
      | Mono | Dropped -> (b, c)
      | Poly ->
        if needed |> List.existsb (fun v -> bv_eq v b.binder_bv)
        then (changed := true; (b, Mono))
        else (b, Poly))
    in
    (!changed, bcs)
  in
  let rec fixpoint (n:int) (bcs:list (binder & bclass)) : ML (list (binder & bclass)) =
    if n <= 0 then bcs
    else let changed, bcs = pass bcs in
         if changed then fixpoint (n - 1) bcs else bcs
  in
  let bcs = fixpoint (List.length bs) bcs in
  (* A type binder that came out of the fixpoint still [Poly] is compiled
     uniformly (section 5.0), so it carries nothing at runtime and is deleted
     from the signature and from every call site -- exactly like an erased
     value binder.  This has to happen *after* the fixpoint, or rule 5 could
     not promote it to [Mono] when a [Mono] binder's type mentions it. *)
  let cs = bcs |> List.map (fun (b, c) ->
    match c with
    | Poly -> if is_type_binder b then Dropped else Poly
    | c -> c) in
  (* Same guard as [erased_binders]: keep one binder rather than turn an impure
     definition into a value.  (A definition all of whose binders are [Mono] has
     the same problem and would need thunking to fix; that is a known gap.) *)
  let flags = keep_one_if_impure env comp (cs |> List.map Dropped?) in
  List.zip cs flags |> List.map (fun (c, dropped) ->
    match c with
    | Dropped -> if dropped then Dropped else Poly
    | c -> c)

let has_mono (cs:list bclass) : ML bool =
  cs |> List.existsb Mono?

let has_dropped (cs:list bclass) : ML bool =
  cs |> List.existsb Dropped?
