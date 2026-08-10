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

(* Rule 2's opt-out.  [@@custard_no_monomorphize] on the class says that its
   instances are runtime values and not compile-time dictionaries, which is the
   truth about [embedding]: [e_list e_sigelt] is computed, stored and passed
   around like any other value, and there is nothing to specialize on.  Without
   the opt-out every function that takes one -- [unembed] is the one that
   matters -- rejects each of its callers under section 3.2b.

   It is the *binder's type* that is consulted, not how the binder was written,
   so it applies to a [{| |}] binder and an explicit one alike. *)
let is_unspecializable_binder (env:TcEnv.env) (b:binder) : ML bool =
  let hd, _ = U.head_and_args_full (U.unrefine (SS.compress b.binder_bv.sort)) in
  match (U.un_uinst hd).n with
  | Tm_fvar fv -> TcEnv.fv_has_attr env fv PC.custard_no_monomorphize_attr
  | _ -> false

(* Does this sort classify types rather than values -- [Type], but also
   [Type -> Type], the kind of the [m] in [class monad (m:Type -> Type)]?

   [eqtype] and [Type0] are abbreviations, not [Tm_type]s, so the sort has to
   be unfolded before it can be recognised.  Getting this wrong is not
   harmless: the parameters of an inductive are exactly its type binders, and
   a missed one becomes an unbound type variable in the emitted type -- or,
   for a higher kind, an unbound *term* variable, because the binder is then
   taken for a runtime one and its uses are compiled as values. *)
let rec is_arity_aux (normed:bool) (env:TcEnv.env) (t:typ) : ML bool =
  let t = SS.compress (U.unrefine t) in
  match t.n with
  | Tm_type _ -> true
  (* Through [arrow_formals_comp], which opens the binders: normalizing a
     codomain with loose de Bruijn indices in it fails outright. *)
  | Tm_arrow _ ->
    let bs, c = U.arrow_formals_comp t in
    is_arity_aux false (TcEnv.push_binders env bs) (U.comp_result c)
  (* Only a name can still be hiding one, and only normalization can tell.
     Paying for it once, at the end, rather than at every step: this runs on
     every binder of every definition the extraction visits. *)
  | Tm_fvar _ | Tm_app _ | Tm_uinst _ ->
    not normed &&
    is_arity_aux true env
      (N.normalize [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                    TcEnv.Beta; TcEnv.Iota;
                    TcEnv.UnfoldUntil delta_constant]
                   env t)
  | _ -> false

let is_arity (env:TcEnv.env) (t:typ) : ML bool = is_arity_aux false env t

let is_type_binder (env:TcEnv.env) (b:binder) : ML bool =
  is_arity env b.binder_bv.sort

(* Of the sorts [is_arity] accepts, the ones of kind [Type] exactly.

   The distinction is the target's, not F*'s.  Every arity binder is erased
   from the value world alike -- that is [is_type_binder] -- but only a binder
   of kind [Type] can become a *parameter* of a target type: neither OCaml nor
   C has a type variable standing for a type constructor, so the [m] of [class
   monad (m:Type -> Type)] can be neither declared nor passed.  Uniform
   compilation (section 5.0) is what makes dropping it sound: [monad m] is
   represented the same way whatever [m] is, and every field whose type
   mentions [m] is already [any].  What is left is a parameterless [monad],
   which is exactly what the fields say. *)
let rec is_star_aux (normed:bool) (env:TcEnv.env) (t:typ) : ML bool =
  match (SS.compress (U.unrefine t)).n with
  | Tm_type _ -> true
  | Tm_fvar _ | Tm_app _ | Tm_uinst _ ->
    not normed &&
    is_star_aux true env
      (N.normalize [TcEnv.AllowUnboundUniverses; TcEnv.EraseUniverses;
                    TcEnv.Beta; TcEnv.Iota;
                    TcEnv.UnfoldUntil delta_constant]
                   env t)
  | _ -> false

let is_type_param (env:TcEnv.env) (b:binder) : ML bool =
  is_star_aux false env b.binder_bv.sort

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

(* The term-level counterpart of [is_type_binder]: a spine whose head no
   declaration describes is filtered with this instead.  Structural, like the
   ML extraction's [is_type]: what a term denotes is decided by its head. *)
let rec is_type_term (env:TcEnv.env) (t:term) : ML bool =
  match (SS.compress t).n with
  | Tm_type _
  | Tm_arrow _
  | Tm_refine _ -> true
  | Tm_uinst (t, _)
  | Tm_ascribed {tm=t}
  | Tm_meta {tm=t} -> is_type_term env t
  | Tm_name bv -> is_arity env bv.sort
  | Tm_fvar fv ->
    (match TcEnv.try_lookup_lid env (S.lid_of_fv fv) with
     | Some ((_, ty), _) -> is_arity env ty
     | None -> false)
  | Tm_app _ -> is_type_term env (fst (U.head_and_args_full t))
  | Tm_abs _ ->
    let bs, body, _ = U.abs_formals t in
    is_type_term (TcEnv.push_binders env bs) body
  | _ -> false

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

(* The sorts of the binders [erased_binders] retains, in order: exactly what a
   caller still has to supply.  Used to type the binders introduced when a
   primitive has to be eta-expanded, which would otherwise be [TAny]. *)
let retained_sorts (env:TcEnv.env) (t:typ) : ML (list typ) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.filter (fun b -> not (is_erased_binder env b))
     |> List.map (fun b -> b.binder_bv.sort)

(* The binders of [t] that are kept but carry no value, so a call site may --
   and should -- pass [()] rather than whatever the source supplies.

   Two kinds.  A unit-shaped binder is the one rule 1 declines to delete, and
   what the source supplies for it can be a [Prims.magic ()] that aborts at
   runtime, or an arbitrarily expensive piece of ghost code.  A *type* binder
   is normally deleted outright, but {!keep_thunk} puts the last one back when
   deleting it would turn the definition into a value; what the source supplies
   for that one is a type, and a type is not a term.  Passing it produces
   either an [Obj.magic ()] (when the argument is a concrete type, which
   happens to work) or a reference to a type variable in value position (when
   it is not, which does not). *)
let unit_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.map (fun b -> U.is_unit b.binder_bv.sort || is_type_binder env b)

let type_binders (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.map (is_type_binder env)

(* The binders that become parameters of the target type, positionally: a
   higher-kinded one is erased like any other type binder but is not one of
   them (see {!is_type_param}). *)
let type_params (env:TcEnv.env) (t:typ) : ML (list bool) =
  let bs, _ = U.arrow_formals_comp t in
  bs |> List.map (is_type_param env)

let classify (env:TcEnv.env) (attrs:list attribute) (t:typ) : ML (list bclass) =
  let bs, comp = U.arrow_formals_comp t in
  let all_mono = U.has_attribute attrs PC.monomorphize_attr in
  let mono_types = Options.custard_monomorphize_types () in
  let init (b:binder) : ML bclass =
    if is_dropped_binder env b || is_unit_binder b                (* rule 1 *)
    then Dropped
    else if U.has_attribute b.binder_attrs PC.monomorphize_attr   (* rule 3 *)
    then Mono
    (* Rule 2's opt-out beats the rules that infer [Mono], and loses to the
       one that is written on the binder itself: a class can say that it is
       not a compile-time dictionary, but it cannot overrule a specific
       binder that asks to be specialized anyway. *)
    else if is_unspecializable_binder env b
    then Poly
    else if all_mono                                              (* rule 3 *)
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
