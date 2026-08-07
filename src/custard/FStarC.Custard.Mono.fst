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
module N     = FStarC.TypeChecker.Normalize

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

let is_type_binder (env:TcEnv.env) (b:binder) : ML bool =
  (* [eqtype] and [Type0] are abbreviations, not [Tm_type]s, so the sort has to
     be unfolded before it can be recognised.  Getting this wrong is not
     harmless: the parameters of an inductive are exactly its type binders, and
     a missed one becomes an unbound type variable in the emitted type. *)
  let sort = N.normalize [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                          TcEnv.Beta; TcEnv.Iota;
                          TcEnv.UnfoldUntil delta_constant]
                         env b.binder_bv.sort in
  match (SS.compress (U.unrefine sort)).n with
  | Tm_type _ -> true
  | _ -> false

(* Rule 1: a non-informative binder carries no runtime value, so it is deleted
   rather than passed.  The *unit-shaped* ones are excluded here, and
   [U.is_unit] is the right test because it treats [unit], [squash p] and
   [_:unit{p}] as the one thing they are.  They are deleted too, but only from
   a *signature*, by [classify] below, where the codomain is in hand: a unit
   binder is also how F* writes a thunk, and dropping the wrong one turns an
   impure function into a value whose effect then runs at module
   initialization.  This predicate is the one applied to the binders that come
   from a definition's own lambdas rather than from its type, where there is no
   codomain to consult and so no way to tell a thunk apart. *)
let is_dropped_binder (env:TcEnv.env) (b:binder) : ML bool =
  let sort = b.binder_bv.sort in
  not (U.is_unit sort) &&
  not (is_type_binder env b) &&
  TcUtil.must_erase_for_extraction env sort

let is_unit_binder (b:binder) : ML bool = U.is_unit b.binder_bv.sort

let is_erased_binder (env:TcEnv.env) (b:binder) : ML bool =
  is_type_binder env b || is_dropped_binder env b

(* The guard that makes deleting a binder from a *definition* safe.  Two things
   can go wrong.  Deleting every binder turns the definition into a value, so
   its body runs at module initialization instead of when it is called, and any
   partial application of it at a call site silently becomes a saturated one.
   And a unit-shaped binder in front of an impure codomain is
   indistinguishable, from the type alone, from the thunk F* writes the same
   way -- [unit -> ML a] and [squash p -> ML a] are the same arrow.

   So the last binder is retained when it is dropped and either the definition
   would otherwise become a value, or it is unit-shaped and the codomain is
   impure.  It carries no information -- its argument is [()] either way, see
   [unit_binders] -- it just keeps the definition a function.  Both the
   signature and the call sites derive their filtering from the same F* type,
   so they agree without communicating.

   The first clause does not test purity, even though a pure body may be run at
   initialization without changing what the program computes, because F*'s
   notion of purity is not Custard's: a Pulse [fn f () : stt unit] is a [Tot]
   function returning an [stt] value, and section 7.2 is what makes it an
   impure arrow.  Keeping the arity is the answer that does not depend on
   which of the two notions is meant. *)
let keep_thunk (env:TcEnv.env) (bs:binders) (c:comp) (flags:list bool) : ML (list bool) =
  let last (l:list 'a) : ML (option 'a) =
    match List.rev l with x :: _ -> Some x | [] -> None in
  let becomes_value = Cons? flags && List.for_all (fun b -> b) flags in
  let is_thunk =
    not (U.is_pure_or_ghost_comp c) &&
    (match last bs with Some b -> is_unit_binder b | None -> false) in
  if last flags = Some true && (becomes_value || is_thunk)
  then (match List.rev flags with
        | _ :: rest -> List.rev (false :: rest)
        | [] -> flags)
  else flags

(* A constructor is a value, so neither hazard applies to it: deleting all of
   its arguments is exactly what a nullary constructor is.  The one case that
   would still be wrong is an impure one, which does not exist. *)
let erased_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.map (is_erased_binder env)

(* The binders of [t] whose value is irrelevant because their type is
   unit-shaped.  These are exactly the ones rule 1 declines to delete, so a
   call site may -- and should -- pass [()] rather than whatever proof term the
   source supplies, which can be a [Prims.magic ()] that aborts at runtime. *)
let unit_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.map (fun b -> U.is_unit b.binder_bv.sort)

let type_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.map (is_type_binder env)

let classify (env:TcEnv.env) (attrs:list attribute) (t:typ) : ML (list bclass) =
  let bs, comp = U.arrow_formals_comp t in
  let all_mono = U.has_attribute attrs PC.monomorphize_attr in
  let mono_types = Options.custard_monomorphize_types () in
  let init (b:binder) : ML bclass =
    if is_dropped_binder env b || is_unit_binder b                (* rule 1 *)
    then Dropped
    else if all_mono                                                   (* rule 3 *)
    || U.has_attribute b.binder_attrs PC.monomorphize_attr        (* rule 3 *)
    || is_tcresolve_binder b                                      (* rule 2 *)
    || is_tcclass_binder env b                                    (* rule 2 *)
    || (mono_types && is_type_binder env b)                           (* rule 4 *)
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
    | Poly -> if is_type_binder env b then Dropped else Poly
    | c -> c) in
  (* Same guard as [erased_binders]: keep the last binder rather than turn the
     definition into a value or delete what may be a thunk.  (A definition all
     of whose binders are [Mono] has the same problem and would need thunking
     to fix; that is a known gap.) *)
  let flags = keep_thunk env bs comp (cs |> List.map Dropped?) in
  List.zip cs flags |> List.map (fun (c, dropped) ->
    match c with
    | Dropped -> if dropped then Dropped else Poly
    | c -> c)

let has_mono (cs:list bclass) : ML bool =
  cs |> List.existsb Mono?

let has_dropped (cs:list bclass) : ML bool =
  cs |> List.existsb Dropped?
