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

let classify (env:TcEnv.env) (attrs:list attribute) (t:typ) : ML (list bclass) =
  let bs, _ = U.arrow_formals_comp t in
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
  fixpoint (List.length bs) bcs |> List.map snd

let has_mono (cs:list bclass) : ML bool =
  cs |> List.existsb Mono?

let has_dropped (cs:list bclass) : ML bool =
  cs |> List.existsb Dropped?
