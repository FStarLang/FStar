(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.Core
(*

This module implements a core typechecker for pure and ghost F* terms.

It expects terms to be elaborated with all implicit arguments and annotated
bound variables, though it also accepts typechecking terms that contain unsolved
unification variables at their introduced types.

Abstractly, the main `check g e` computes
  
     g |- e : t | p

where a term `e` is typed at `t` in environment `g`,
provided the  guard `p` is provable in `g` (i.e., g |= p). 

We write `g |- e : t` for `g |- e : t | True`

A main nuance is in its use of caches, of two kinds:

1. A term typing cache

Each sub-call to check memoizes the result `g |- e : t` and returns the guard
`p` to be proven.

Subsequent calls to `check g' e'` looks up `e'` in the cache, and if it findds
`g |- e : t`, checks that `g'` is an extension of `g`, and if so, records a
cache hit and returns `g' |- e : t`.


2. A guard cache

When issuing a guard (e.g,. as the result of checking a subtyping relation 
`g |- t <: t' | p`), we also cache `g |= p`.

If a guard is issued later for `g' |= p`, we check if `g |= p` is cached and if
`g'` extensions `g`, we record a cache hit and do not emit the guard.

Guards are not proven immediately; instead they are accumulated and returned to
the caller to be proven later. To accomodate this API, we have two levels of
caches:

- A functional cache: cache_t.term_map and cache_t.guard_map
   
   These caches are initialized to empty at each call into the public API of the
   checker, e.g, check_term.

   The call to check_term populates the caches as it checks a term and returns
   guard to the caller. 

   The main invariant is the the provability of the returned guard implies the
   provability of all cached guards in the guard_map; and, consequently, the
   typing of all terms in the term_map.

   Once the returned guard is discharged by the caller (e.g, by calling SMT), a
   callback into this Core checker notifies it that the returned guard has been
   proven, and which point, the term_map and guard_map are promoted to the
   second level imperative cache, described next.

- The second level cache accumulates entries across multiple calls to this
  Core checker. Every entry in this cache contains guards that have already been
  proven, and contains terms whose typing has already been established.

  The second level cache is explicit cleared by called clear_memo_table, which 
  FStarC.TypeChecker.Tc does at each top-level declaration.

Organization:

  The checker is split into modules, each depending only on those above it:

  - Core.Base: the vocabulary: debug toggles, effects ([eff]), the
    environment ([env]), facts, relations, error contexts and errors.
  - Core.Monad: the [result] monad, in which a computation runs in a
    context, threads the functional cache, and fails or succeeds with a
    guard; and its combinators.
  - Core.Binders: the initial environment, and opening binders, terms,
    patterns and branches.
  - Core.Effects: the effect lattice as the checker sees it.
  - Core.Util: utilities on terms, types and patterns that do not call back
    into the checker.
  - Core.Facts: the facts about terms that the checker gathers, and assumes
    in guards.
  - Core.Cache: the term and guard caches, and the memo of failed relations.
  - Core.Guard: emitting guards, and closing, weakening and labeling them.

  This module has the checker proper, a single mutually recursive
  definition, in sections: relating types; checking terms; types,
  universes and computation types; checking against an expected type;
  [let]; [let rec]; and [match]. The public API follows it.

Dependencies:

  This checker does not depend on the elaborator (TcTerm, TcUtil) or on the
  unifier (Rel). The utilities it shares with them are in small modules:
  VCUtil (labels and simplification of VCs), UnivEq (universe equality),
  UniverseOf (the types of constants and syntactic universe computation),
  Termination (the refined types of recursive definitions) and CommonBase.
  Still, terms it is given may have been elaborated by TcTerm, and it
  re-checks them; and a few Env callbacks (e.g.
  [env.typeof_well_typed_tot_or_gtot_term], used by
  Termination) dispatch to TcTerm at runtime, only to compute terms that
  this checker then checks.

*)
open FStarC.TypeChecker.CommonBase
open FStarC
open FStar.List.Tot
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.Errors.Msg { fquotes }
module Env = FStarC.TypeChecker.Env
module S = FStarC.Syntax.Syntax
module R = FStarC.Range
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module PC = FStarC.Parser.Const
module I = FStarC.Ident
module BU = FStarC.Util
module VCUtil = FStarC.TypeChecker.VCUtil
module UnivEq = FStarC.TypeChecker.UnivEq
module UniverseOf = FStarC.TypeChecker.UniverseOf
module Termination = FStarC.TypeChecker.Termination
module Err = FStarC.TypeChecker.Err
module Hash = FStarC.Syntax.Hash
module Subst = FStarC.Syntax.Subst
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
module Visit = FStarC.Syntax.Visit

open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Class.Tagged
open FStarC.Class.PP
open FStarC.Syntax.Print {}

open FStarC.Pprint
open FStarC.Errors.Msg { text }

open FStarC.TypeChecker.Core.Base
open FStarC.TypeChecker.Core.Monad
open FStarC.TypeChecker.Core.Binders
open FStarC.TypeChecker.Core.Effects
open FStarC.TypeChecker.Core.Util
open FStarC.TypeChecker.Core.Facts
open FStarC.TypeChecker.Core.Cache
open FStarC.TypeChecker.Core.Guard
module Base = FStarC.TypeChecker.Core.Base
module Effects = FStarC.TypeChecker.Core.Effects
module Cache = FStarC.TypeChecker.Core.Cache
module HashTable = FStarC.HashTable

(*** Public definitions from the submodules, and the goal counter *)

let goal_ctr = mk_ref 0

let get_goal_ctr () = !goal_ctr

let incr_goal_ctr () = let v = !goal_ctr in goal_ctr := v + 1; v + 1

let error = Base.error
let print_error = Base.print_error
instance showable_error : showable error = Base.showable_error
let print_error_short = Base.print_error_short
let error_code = Base.error_code
let error_message = Base.error_message
let error_range = Base.error_range

let clear_memo_table = Cache.clear_memo_table

let empty_token () = ()

let commit_guard (cb:guard_commit_token_cb) : ML unit = cb()

let commit_guard_and_tok_opt (t:option guard_and_tok_t) =
  match t with
  | None -> ()
  | Some (_, tok) -> commit_guard tok

let is_non_informative = Effects.is_non_informative

instance showable_tot_or_ghost = {
    show = (function
            | E_Total -> "E_Total"
            | E_Ghost -> "E_Ghost");
}

instance showable_side = {
    show = (function
            | Left -> "Left"
            | Right -> "Right"
            | Both -> "Both"
            | Neither -> "Neither");
}

let maybe_relate_after_unfolding (g:Env.env) t0 t1 : ML side =
  let dd0 = Env.delta_depth_of_term g t0 in
  let dd1 = Env.delta_depth_of_term g t1 in

  if dd0 = dd1 then
    Both
  else if CommonBase.delta_depth_greater_than dd0 dd1 then
    Left
  else
    Right

(*** The checker *)

(** Relating types:

     G |- t0 <: t1 | p     (or G |- t0 = t1 | p)

    and, with a witness [e] of the subtyping,

     G |- e : t0 <: t1 | p *)

let rec check_relation' (g:env) (rel:relation) (t0 t1:typ)
  : ML (result unit)
  = let err (lbl:string) =
        match rel with
        | EQUALITY ->
          fail [
            parens (text lbl) ^/^ text "not equal terms:"
            ^/^ fquotes (pp t0)
            ^/^ text "<>"
            ^/^ fquotes (pp t1)
          ]
        | _ ->
          fail [
            parens (text lbl)
            ^/^ fquotes (pp t0)
            ^/^ text "is not a subtype of"
            ^/^ fquotes (pp t1)
          ]
    in

    let! guard_not_ok = guard_not_allowed in
    let guard_ok = not guard_not_ok in
    let head_matches t0 t1
      : ML bool
      = let head0 = U.leftmost_head t0 in
        let head1 = U.leftmost_head t1 in
        match (U.un_uinst head0).n, (U.un_uinst head1).n with
        | Tm_fvar fv0, Tm_fvar fv1 -> fv_eq fv0 fv1
        | Tm_name x0, Tm_name x1 -> bv_eq x0 x1
        | Tm_constant c0, Tm_constant c1 -> equal_term head0 head1
        | Tm_type _, Tm_type _
        | Tm_arrow _, Tm_arrow _
        | Tm_match _, Tm_match _ -> true
        | _ -> false
    in
    let which_side_to_unfold t0 t1 =
      maybe_relate_after_unfolding g.tcenv t0 t1 in
    (* As [Rel] when SMT is allowed: a recursive definition (e.g.
       [let rec type_of_nat (n:nat) = bool]) may be unfolded too. *)
    (* An unfolding stuck on a match (e.g. of a recursive definition applied
       to a variable) is only taken when [allow_stuck] and the other side is
       a match already: relating two such unfoldings would relate their
       branches, i.e. the definition applied to the pattern variables, which
       unfold again, without end. *)
    let is_match (t:term) : ML bool =
      Tm_match? (Subst.compress (U.unascribe (U.unmeta t))).n
    in
    let unfold_rec_head (allow_stuck:bool) (other:term) (t:term) : ML (option term) =
      match (U.un_uinst (U.leftmost_head t)).n with
      | Tm_fvar fv
          when None? (Env.lookup_nonrec_definition [Env.Unfold delta_constant] g.tcenv fv.fv_name)
            && Some? (Env.lookup_definition [Env.Unfold delta_constant] g.tcenv fv.fv_name) ->
        let t' = N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF; Env.Primops;
                              Env.Beta; Env.Iota; Env.Zeta] g.tcenv t in
        if TEQ.eq_tm g.tcenv t t' = TEQ.Equal then None
        else if is_match (U.leftmost_head t') && not (allow_stuck && is_match other) then None
        else Some t'
      | _ -> None
    in
    (* As [Rel] ([head_matches_delta]), which unfolds with [UnfoldUntil
       delta_constant]: a [match] whose scrutinee only reduces after
       unfolding definitions in it, e.g. [parse_array_kind k 8 2] unfolded
       to [match fldata_array_precond k 8 2 && .. with | true -> .. | _ ->
       ..], is reduced by computing that scrutinee. [Zeta] is left out, as
       in [Rel]. The reduction is kept only if a branch is taken. Reducing
       to head normal form leaves the arguments of constructors as they are,
       e.g. [Some k.lo], on which a primitive equality is stuck, in the
       scrutinee or in that of a nested [match] in the branch taken; if no
       branch is taken then, the [match] is normalized fully. *)
    let reduce_match (t:term) : ML (option term) =
      let reduced t' = if is_match (U.leftmost_head t') then None else Some t' in
      if not (is_match t) then None
      else
        let t' = N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF; Env.Primops;
                              Env.Beta; Env.Iota] g.tcenv t in
        match reduced t' with
        | Some t' -> Some t'
        | None ->
          reduced (N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.Primops;
                                Env.Beta; Env.Iota] g.tcenv t)
    in
    let unfold_head_with (allow_rec:bool) (allow_stuck:bool) (other:term) (t:term) : ML (option term) =
      match N.maybe_unfold_head g.tcenv t with
      | Some t' -> (
        match reduce_match t' with
        | Some t'' -> Some t''
        | None -> Some t')
      | None ->
        match reduce_match t with
        | Some t' -> Some t'
        | None -> if allow_rec then unfold_rec_head allow_stuck other t else None
    in
    let maybe_unfold_side'' (allow_rec:bool) (allow_stuck:bool) side t0 t1
      : ML (option (term & term))
      = let unfold_head other t = unfold_head_with allow_rec allow_stuck other t in
        Profiling.profile (fun _ ->
        match side with
        | Neither -> None
        | Both -> (
          match unfold_head t1 t0,
                unfold_head t0 t1
          with
          | Some t0, Some t1 -> Some (t0, t1)
          | Some t0, None -> Some (t0, t1)
          | None, Some t1 -> Some (t0, t1)
          | _ -> None
        )
        | Left -> (
          match unfold_head t1 t0 with
          | Some t0 -> Some (t0, t1)
          | _ -> None
        )
        | Right -> (
          match unfold_head t0 t1 with
          | Some t1 -> Some (t0, t1)
          | _ -> None
        ))
        None
        "FStarC.TypeChecker.Core.maybe_unfold_side"
    in
    let maybe_unfold_side' (allow_rec:bool) side t0 t1 = maybe_unfold_side'' allow_rec true side t0 t1 in
    let maybe_unfold_side side t0 t1 = maybe_unfold_side' guard_ok side t0 t1
    in
    let maybe_unfold t0 t1
      : result (option (term & term))
      = if! unfolding_ok
        then return (maybe_unfold_side (which_side_to_unfold t0 t1) t0 t1)
        else return None
    in
    let emit_guard t0 t1 =
       match rel with
       | SUBTYPING wit ->
         (* [t0] and [t1] are types, and it suffices
            that the term at hand (or any term of type [t0]) has type [t1]. *)
         let! u0 = universe_of_well_typed_term g t0 in
         let! u1 = universe_of_well_typed_term g t1 in
         begin match wit with
         | Some (tm, fs) -> witness_guard g fs (U.mk_has_type [u0; u1] t0 tm t1)
         | None ->
           let x = S.new_bv None t0 in
           guard g (U.mk_forall u0 x (U.mk_has_type [u0; u1] t0 (S.bv_to_name x) t1))
         end
       | EQUALITY ->
         let! _, t_typ, _ = with_context "checking lhs while emitting guard" None (fun _ -> do_check g t0) in
         let! u = universe_of_well_typed_term g t_typ in
         guard g (U.mk_eq2 u t_typ t0 t1)
    in
    let fallback t0 t1 =
      if guard_ok
      then if equatable g t0
            || equatable g t1
            (* e.g. [x:(match sw with ...){p} <: int] *)
            || equatable g (U.unrefine t0)
            || equatable g (U.unrefine t1)
           then emit_guard t0 t1
           else err "not equatable"
      else err "guards not allowed"
    in
    let maybe_unfold_side_and_retry side t0 t1 =
      let is_app (t:term) : ML bool =
        match (Subst.compress (U.unascribe (U.unmeta t))).n with
        | Tm_app _ | Tm_fvar _ | Tm_uinst _ -> true
        | _ -> false
      in
      let is_match_or_abs (t:term) : ML bool =
        match (Subst.compress (U.unascribe (U.unmeta t))).n with
        | Tm_match _ | Tm_abs _ -> true
        | _ -> false
      in
      let is_refine (t:term) : ML bool =
        match (Subst.compress (U.unascribe (U.unmeta t))).n with
        | Tm_refine _ -> true
        | _ -> false
      in
      let has_definition (t:term) : ML bool =
        match (U.un_uinst (U.leftmost_head t)).n with
        | Tm_fvar fv -> Some? (Env.lookup_definition [Env.Unfold delta_constant] g.tcenv fv.fv_name)
        | Tm_name _ | Tm_bvar _ -> false
        | _ -> true
      in
      let rec bases_match (n:int) (t0:term) (t1:term) : ML bool =
        (* Whether the base types of two refinements come to have the same
           head by unfolding applications, e.g. [nat] and [int], but not
           [sum_type s] (which unfolds to a [match] on [s]) and [t']. *)
        let t0 = U.unascribe (U.unmeta (U.unrefine t0)) in
        let t1 = U.unascribe (U.unmeta (U.unrefine t1)) in
        if head_matches t0 t1 then true
        else if n = 0 || not (is_app t0 && is_app t1) then false
        else match maybe_unfold_side' false (which_side_to_unfold t0 t1) t0 t1 with
             | None -> false
             | Some (t0, t1) -> bases_match (n - 1) t0 t1
      in
      let rec unfold_to_match (n:int) (t0:term) (t1:term) : ML bool =
        if head_matches t0 t1 then true
        else if (is_match t0 && is_app t1) || (is_app t0 && is_match t1) then
          (* One side unfolded to a [match], the other is still an
             application: unfold that further. If it has no definition
             (e.g. [p ** q] against [match c with | true -> p ** q | ...],
             the unfolding of a [let side .. = if c then p ** q else ..]), the
             equation between it and the [match] is what the SMT solver can
             prove, by cases, while one between it and the folded side would
             need the solver to unfold that, and then to relate the
             abstractions in its body (e.g., [exists* x. ..]) to those of
             the other side, which are encoded apart. *)
          let side = if is_app t0 then Left else Right in
          match (if n = 0 then None else maybe_unfold_side' false side t0 t1) with
          | Some (t0, t1) -> unfold_to_match (n - 1) (U.unascribe (U.unmeta t0)) (U.unascribe (U.unmeta t1))
          | None -> not (has_definition (if is_app t0 then t0 else t1))
        else if is_refine t0 || is_refine t1 then
          (* One side unfolded to a refinement, e.g. [pfr f] to [x:int{f x
             == true}] against [ct k] for a recursive [ct]: unfolding only
             helps if the base type of the refinement comes to match the
             other side, e.g. [nat] against [int]. Otherwise the guard is
             better stated on the terms as they are, [pfr f == ct k], which
             the SMT solver can prove from the equations of [ct]: the
             encoding of the refinement in it would be a fresh term,
             unrelated to that of the body of [pfr]. *)
          bases_match n t0 t1
        else if not (is_app t0 && is_app t1) then
          (* Unfolding reached a [match] or a [fun], e.g. [maybe_close
             a c] against [close a]: relating that to the other side
             can only produce a guard about the unfoldings, an equation
             between a [fun] and a [match] which the SMT solver can
             seldom prove. Treat it as a mismatch, so that the guard is
             stated on the terms as they are. *)
          not (is_match_or_abs t0 || is_match_or_abs t1)
        else if n = 0 then false
        else match maybe_unfold_side' false (which_side_to_unfold t0 t1) t0 t1 with
             | None -> false
             | Some (t0, t1) -> unfold_to_match (n - 1) (U.unascribe (U.unmeta t0)) (U.unascribe (U.unmeta t1))
      in
      (* As [Rel] ([head_matches_delta]): when the unfoldings of two
         applications never come to have the same head, the guard is stated
         on the terms as they are, not on their unfoldings, which the SMT
         patterns of lemmas about them would not match, e.g. [denote_term
         (elab_exp (open_exp e x)) == open_term (denote_term (elab_exp e)) x]
         where [open_term] unfolds to an application of another recursive
         function. *)
      let is_name (t:term) : ML bool =
        match (Subst.compress (U.unascribe (U.unmeta t))).n with
        | Tm_name _ -> true
        | _ -> false
      in
      (* Likewise when one side is a variable, e.g. the index [g] of a
         pattern-bound [h:typing g e t] against [extend_gen x t_x g']: the
         unfolding of the other side can only help if it closes the relation
         outright; otherwise [g == extend_gen x t_x g'] is what the SMT
         solver can prove, from the inversion of [h]'s type. *)
      (* Whether unfolding the other side of a variable, recursive
         definitions included, closes the relation outright, e.g. [l] and
         [[] @ l] under [--no_smt]: [op_At] unfolds to [append [] l], which
         only reduces to [l] by unfolding [append]. [Zeta] is used only
         here, in a single normalization to head normal form of the
         non-variable side, and not in the general unfolding of the heads
         of applications: there, [match]es of recursive definitions could
         unfold forever, e.g. relating [f l] and [g l] for two recursive
         functions that are equal by a lemma. *)
      let closes_with_zeta () =
        let zeta t =
          if is_name t then t
          else N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.HNF; Env.Primops;
                            Env.Beta; Env.Iota; Env.Zeta] g.tcenv t
        in
        let t0'' = zeta t0 in
        let t1'' = zeta t1 in
        if U.term_eq t0 t0'' && U.term_eq t1 t1''
        then err "no unfolding"
        else no_guard (check_relation g rel t0'' t1'')
      in
      (* Neither side unfolds, e.g. [k0.parser_kind_low + k1.parser_kind_low]
         (a primitive operation on projections of definitions) against the
         literal [25]. As [Rel], whose guard [k0.parser_kind_low +
         k1.parser_kind_low == 25] is normalized away when discharged, the
         relation is closed by evaluating both sides, if one of them is a
         literal. [Zeta] is left out. *)
      let closes_by_evaluation () =
        let is_const (t:term) : ML bool =
          match (Subst.compress (U.unascribe (U.unmeta t))).n with
          | Tm_constant _ -> true
          | _ -> false
        in
        if not (is_const t0 || is_const t1) then err "no evaluation"
        else
          let ev t =
            N.normalize [Env.UnfoldUntil delta_constant; Env.Weak; Env.Primops;
                         Env.Beta; Env.Iota] g.tcenv t
          in
          let t0'' = ev t0 in
          let t1'' = ev t1 in
          if U.term_eq t0 t0'' && U.term_eq t1 t1''
          then err "no evaluation"
          else no_guard (check_relation g rel t0'' t1'')
      in
      let retry_unfolded t0' t1' =
        if is_name t0 || is_name t1
        then handle_with (no_guard (check_relation g rel t0' t1'))
               (fun _ -> handle_with (closes_with_zeta ())
               (fun _ -> handle_with (fallback t0 t1) (fun _ -> check_relation g rel t0' t1')))
        else if is_app t0 && is_app t1
            && not (unfold_to_match 16 (U.unascribe (U.unmeta t0')) (U.unascribe (U.unmeta t1')))
        then handle_with (no_guard (check_relation g rel t0' t1'))
               (fun _ -> handle_with (fallback t0 t1) (fun _ -> check_relation g rel t0' t1'))
        else check_relation g rel t0' t1'
      in
      if! unfolding_ok then
        match maybe_unfold_side' false side t0 t1 with
        | Some (t0', t1') when not guard_ok -> check_relation g rel t0' t1'
        | Some (t0', t1') -> retry_unfolded t0' t1'
        | None ->
          (* Unfolding a recursive definition (which needs a guard, for the
             SMT solver may then prove the relation from its equations) is
             only worth it if it closes the relation outright, e.g. when the
             unfolding reduces by iota. Otherwise the guard is stated on the
             terms as they are. This is tried even when guards are not
             allowed, e.g. relating [natlt n & unit] to [abs (ICons n INil)]
             for a recursive [abs] while trying to relate the arguments of
             two applications without a guard. *)
          match maybe_unfold_side'' true guard_ok side t0 t1 with
          | Some (t0', t1') ->
            handle_with (no_guard (check_relation g rel t0' t1')) (fun _ -> fallback t0 t1)
          | None -> handle_with (closes_by_evaluation ()) (fun _ -> fallback t0 t1)
      else
        fallback t0 t1
    in
    let maybe_unfold_and_retry t0 t1 =
      maybe_unfold_side_and_retry (which_side_to_unfold t0 t1) t0 t1
    in
    let unfoldable_head (t:term) : bool =
      match t.n with
      | Tm_app _ | Tm_fvar _ | Tm_uinst _ -> true
      | _ -> false
    in
    let abs_vs_unfoldable side t0 t1 =
      if! unfolding_ok then
        match maybe_unfold_side' false side t0 t1 with
        | Some (t0', t1') -> check_relation g rel t0' t1'
        | None -> fallback t0 t1
      else fallback t0 t1
    in
    let beta_iota_reduce t =
        let t = Subst.compress t in
        let t = N.normalize [Env.HNF; Env.Weak; Env.Beta; Env.Iota; Env.Primops] g.tcenv t in
        match t.n with
        | Tm_refine _ ->
          U.flatten_refinement t
        | _ -> t
    in
    let beta_iota_reduce t =
        Profiling.profile
          (fun () -> beta_iota_reduce t)
          None
          "FStarC.TypeChecker.Core.beta_iota_reduce"
    in
    let t0 = Subst.compress (beta_iota_reduce t0) |> U.unlazy_emb in
    let t1 = Subst.compress (beta_iota_reduce t1) |> U.unlazy_emb in
    let check_relation g rel t0 t1 =
      with_context "check_relation" (Some (CtxRel t0 rel t1))
        (fun _ -> check_relation g rel t0 t1)
    in
    if equal_term t0 t1 then return ()
    else
      match t0.n, t1.n with
      | Tm_type u0, Tm_type u1 ->
        // when g.allow_universe_instantiation ->
        // See above remark regarding universe instantiations
        if UnivEq.teq_univs g.tcenv [u0] [u1]
        then return ()
        else err "Unequal universes"

      | Tm_meta {tm=t0; meta=Meta_pattern _}, _
      | Tm_meta {tm=t0; meta=Meta_named _}, _
      | Tm_meta {tm=t0; meta=Meta_labeled _}, _
      | Tm_meta {tm=t0; meta=Meta_desugared _}, _
      | Tm_ascribed {tm=t0}, _ ->
        check_relation g rel t0 t1

      | _, Tm_meta {tm=t1; meta=Meta_pattern _}
      | _, Tm_meta {tm=t1; meta=Meta_named _}
      | _, Tm_meta {tm=t1; meta=Meta_labeled _}
      | _, Tm_meta {tm=t1; meta=Meta_desugared _}
      | _, Tm_ascribed {tm=t1} ->
        check_relation g rel t0 t1

      | Tm_uinst (f0, us0), Tm_uinst(f1, us1) ->
        if equal_term f0 f1
        then ( //heads are equal, equate universes
             if UnivEq.teq_univs g.tcenv us0 us1
             then return ()
             else err "Unequal universe instantiations"
        )
        else maybe_unfold_and_retry t0 t1

      | Tm_fvar _, Tm_fvar _ ->
        maybe_unfold_and_retry t0 t1


      (* [squash p] is definitionally [_:unit{p}], so relating two squashed
         propositions by subtyping is an implication between them. Without this
         rule, the congruence rule for applications below would instead demand
         that the two propositions be *equal*, which is much too strong: it is
         what a caller runs into whenever the postcondition of a lemma is not
         syntactically the goal it is used to justify. *)
      | _, _ when SUBTYPING? rel
               && guard_ok
               && Some? (U.is_squash t0)
               && Some? (U.is_squash t1) ->
        let p0 = Some?.v (U.is_squash t0) in
        let p1 = Some?.v (U.is_squash t1) in
        if equal_term p0 p1
        then return ()
        else (
          match rel with
          | SUBTYPING (Some (_, fs)) -> witness_guard g fs (U.mk_imp p0 p1)
          | _ -> guard g (U.mk_imp p0 p1)
        )

      | Tm_refine {b=x0; phi=f0}, Tm_refine {b=x1; phi=f1} ->
        if head_matches x0.sort x1.sort
        then (
          (* Subtyping suffices for the sorts, e.g. arrows: refinements are
             covariant. *)
          check_relation g rel x0.sort x1.sort ;!
          let! u = universe_of_well_typed_term g x0.sort in
          let g0 = g in
          let g, b, f0 = open_term g (S.mk_binder x0) f0 in
          let f1 = Subst.subst [DB(0, b.binder_bv)] f1 in
            (match! guard_not_allowed with
             | true ->
               (* Or else equal once normalized, e.g. when a tactic
                  normalized one of them (with [compute ()]) but not the
                  other, which is too costly to try first. *)
               let normalized_equal () : ML bool =
                 let n (t:term) : ML term =
                   N.normalize [Env.Beta; Env.Iota; Env.Zeta; Env.Primops;
                                Env.UnfoldUntil S.delta_constant; Env.Unascribe]
                               (Env.push_bv g.tcenv b.binder_bv) t in
                 (* Up to ascriptions (e.g. the [prop] ascription in
                    unfolded [b2t]) and the association of conjunctions,
                    which [U.flatten_refinement] and the normalizer differ on. *)
                 let rec conjuncts (phi:term) : ML (list term) =
                   let hd, args = U.head_and_args_full phi in
                   match (U.un_uinst hd).n, args with
                   | Tm_fvar fv, [(a, _); (b, _)] when S.fv_eq_lid fv PC.and_lid ->
                     conjuncts a @ conjuncts b
                   | _ -> [phi]
                 in
                 let strip = Visit.visit_term false (fun t ->
                   match t.n with
                   | Tm_ascribed {tm} -> tm
                   | Tm_meta {tm} -> tm
                   | _ -> t) in
                 let cs0, cs1 = conjuncts (strip (n f0)), conjuncts (strip (n f1)) in
                 List.length cs0 = List.length cs1 &&
                 List.forall2 equal_term cs0 cs1
               in
               with_binders g0 [b] [u]
                 (handle_with
                    (check_relation g EQUALITY f0 f1)
                    (fun _ ->
                      if normalized_equal () then return ()
                      else check_relation g EQUALITY f0 f1))

             | _ ->
               match rel with
               | EQUALITY ->
                 (* As [Rel]: the refinements are equal if they are
                    syntactically so, or else if they are equivalent;
                    decomposing them further with guards would demand more,
                    e.g. [xs == f xs] for [x < length xs <==> x < length (f xs)]. *)
                 with_binders g0 [b] [u]
                   (handle_with
                      (no_guard (check_relation g EQUALITY f0 f1))
                      (fun _ -> guard g (U.mk_iff f0 f1)))

               | SUBTYPING (Some (tm, fs)) ->
                 witness_guard g0 fs (Subst.subst [NT(b.binder_bv, tm)] (U.mk_imp f0 f1))

               | SUBTYPING None ->
                 guard g0 (U.mk_forall u b.binder_bv (U.mk_imp f0 f1)))
        )
        else (
          match! maybe_unfold x0.sort x1.sort with
          | None ->
            if !dbg then
              Format.print2 "Cannot match ref heads %s and %s\n" (show x0.sort) (show x1.sort);
            fallback t0 t1
          | Some (t0, t1) ->
            let lhs = S.mk (Tm_refine {b={x0 with sort = t0}; phi=f0}) t0.pos in
            let rhs = S.mk (Tm_refine {b={x1 with sort = t1}; phi=f1}) t1.pos in
            check_relation g rel (U.flatten_refinement lhs) (U.flatten_refinement rhs)
        )

      | Tm_refine {b=x0; phi=f0}, _ ->
        if head_matches x0.sort t1
        then (
          (* For subtyping, we just check that x0.sort <: t1. But for equality,
          we must show that the refinement on the LHS is constantly true. *)
          if EQUALITY? rel then (
            let! u0 = universe_of_well_typed_term g x0.sort in
            let g0 = g in
            let g, b0, f0 = open_term g (S.mk_binder x0) f0 in
            if! guard_not_allowed then
              with_binders g0 [b0] [u0]
                (check_relation g EQUALITY U.t_true f0)
            else (
              with_binders g0 [b0] [u0]
                (handle_with
                    (no_guard (check_relation g EQUALITY U.t_true f0))
                    (fun _ -> guard g f0))
            )
          ) else return ();!
          check_relation g rel x0.sort t1
        )
        else (
          match! maybe_unfold x0.sort t1 with
          | None -> fallback t0 t1
          | Some (t0, t1) ->
            let lhs = S.mk (Tm_refine {b={x0 with sort = t0}; phi=f0}) t0.pos in
            check_relation g rel (U.flatten_refinement lhs) t1
        )

      | _, Tm_refine {b=x1; phi=f1} ->
        if head_matches t0 x1.sort
        then (
          let! u1 = universe_of_well_typed_term g x1.sort in
          check_relation g rel t0 x1.sort ;!
          let g0 = g in
          let g, b1, f1 = open_term g (S.mk_binder x1) f1 in
          if! guard_not_allowed then
            with_binders g0 [b1] [u1]
              (check_relation g EQUALITY U.t_true f1)
          else (
            match rel with
            | EQUALITY ->
              with_binders g0 [b1] [u1]
                (handle_with
                    (no_guard (check_relation g EQUALITY U.t_true f1))
                    (fun _ -> guard g f1))

            | SUBTYPING (Some (tm, fs)) ->
                 let f1 = Subst.subst [NT(b1.binder_bv, tm)] f1 in
                 (* A precondition ([unit <: squash p]): TcTerm simplifies its
                    guard on its own, as it creates it
                    ([value_check_expected_typ]), which unfolds an [unfold]
                    abbreviation at its head, e.g. [normal p] into the
                    [norm] request it stands for. A tactic processing the
                    VC may depend on it. *)
                 let f1 = if U.is_unit x1.sort then VCUtil.simplify_vc false g0.tcenv f1 else f1 in
                 witness_guard g0 fs f1

            | SUBTYPING None ->
                 (* Over a fresh (unnamed) variable. *)
                 let x = S.new_bv (Some (S.range_of_bv b1.binder_bv)) b1.binder_bv.sort in
                 let f1 = Subst.subst [NT(b1.binder_bv, S.bv_to_name x)] f1 in
                 guard g0 (U.mk_forall u1 x f1)
          )
        )
        else (
          match! maybe_unfold t0 x1.sort with
          | None -> fallback t0 t1
          | Some (t0, t1) ->
            let rhs = S.mk (Tm_refine {b={x1 with sort = t1}; phi=f1}) t1.pos in
            check_relation g rel t0 (U.flatten_refinement rhs)
        )

      (* An abstraction and a term that is not one: as in [Rel]
         ([head_matches_delta]), the latter is unfolded, e.g. [non_neg_inv r]
         to [fun m -> exists v. r == v] (tests/bug-reports/closed/Bug2002).
         There is no eta rule: [fun (x:a) -> f x] is not equal to [f], whose
         domain may be larger than [a] (see FStar.FunctionalExtensionality
         and tests/micro-benchmarks/Test.FunctionalExtensionality). *)
      | Tm_abs _, _ when unfoldable_head t1 ->
        abs_vs_unfoldable Right t0 t1
      | _, Tm_abs _ when unfoldable_head t0 ->
        abs_vs_unfoldable Left t0 t1

      | Tm_uinst _, _
      | Tm_fvar _, _
      | Tm_app _, _
      | _, Tm_uinst _
      | _, Tm_fvar _
      | _, Tm_app _ ->
        let head_matches = head_matches t0 t1 in
        let head0, args0 = U.leftmost_head_and_args t0 in
        let head1, args1 = U.leftmost_head_and_args t1 in
        if not (head_matches && List.length args0 = List.length args1)
        then maybe_unfold_and_retry t0 t1
        else (
          (* If we're proving equality, SMT queries are ok, and either head
             is equatable:
              - first try proving equality structurally, without a guard.
              - if that fails, then emit an SMT query
             This is designed to be able to prove things like `v.v1 == u.v1`
             first by trying to unify `v` and `u` and if it fails
             then prove `v.v1 == u.v1` *)
          let compare_head_and_args () =
            handle_with
              (check_relation g EQUALITY head0 head1 ;!
               check_relation_args g EQUALITY args0 args1)
              (fun _ -> maybe_unfold_side_and_retry Both t0 t1)
          in
          let abs_args =
            List.length args0 = List.length args1 &&
            BU.for_some (fun ((a0, _), (a1, _)) ->
              Tm_abs? (Subst.compress a0).n && Tm_abs? (Subst.compress a1).n)
              (List.zip args0 args1)
          in
          if guard_ok &&
            (EQUALITY? rel) && 
            (equatable g t0 || equatable g t1)
          then (
            (* An equation between two applications with abstractions as
               corresponding arguments (or terms with binders, as arguments
               of their arguments: see [args_contain_binders]), e.g.
               [on_domain a f == on_domain a g],
               is beyond the SMT solver without extensionality. As [Rel]
               does, the arguments, and so the bodies of the abstractions,
               may be related under their binder; but that is sufficient
               rather than necessary (e.g., [False == p x] needs
               propositional extensionality, while [on_domain a (fun _ ->
               False) == on_domain a p] may be a hypothesis), so either may
               be proven. *)
            let args_or_eq () : result unit =
              with_guard (compare_head_and_args ()) (function
                | Inr err -> fail_propagate err
                | Inl ((), None) -> return ()
                | Inl ((), Some phi) ->
                  let! _, t_typ, _ = do_check g t0 in
                  let! u = universe_of_well_typed_term g t_typ in
                  reemit_guard g (U.mk_disj phi (U.mk_eq2 u t_typ t0 t1)))
            in
            handle_with 
              (no_guard (compare_head_and_args ()))
              (fun _ ->
                if abs_args || args_contain_binders t0 || args_contain_binders t1
                then handle_with (args_or_eq ()) (fun _ -> emit_guard t0 t1)
                else emit_guard t0 t1)
          )
          else if guard_ok
          then (
            (* E.g. [fin n <: fin (n + m)], or [swap_for xs == swap_for (f xs)]
               where [swap_for xs] unfolds to a refinement mentioning only
               [length xs]: rather than demanding that the arguments be equal,
               which may well be false, try relating the unfoldings, as [Rel]
               does, before settling for that. But the arguments may also be
               provably equal where the unfoldings are not (e.g. equal
               sequences given by a lemma, where the unfoldings quantify
               over their indices), so if both need a guard, either suffices,
               unless that of the unfoldings is quantifier-free, e.g. [i < n
               ==> i < n + m], in which case it is the only guard. *)
            handle_with
              (no_guard (check_relation g EQUALITY head0 head1 ;!
                         check_relation_args g EQUALITY args0 args1))
              (fun _ ->
                match! maybe_unfold t0 t1 with
                | Some (t0', t1') ->
                  let unfolded () = check_relation g rel t0' t1' in
                  let argwise () =
                    check_relation g EQUALITY head0 head1 ;!
                    check_relation_args g EQUALITY args0 args1
                  in
                  (* In an equation with abstractions as corresponding
                     arguments, e.g. [forevery (fun i -> p i) == forevery
                     (fun i -> q i)], the unfoldings only relate the same
                     abstractions again, deeper down: offering both would
                     duplicate the argument-wise guard at each level of
                     nesting. (Not so for subtyping, e.g. [st pre post <: st
                     pre' post'], where the unfoldings may be related by
                     implications, but the arguments only by equations.) *)
                  (* A head with the [unifier_hint_injective] attribute,
                     e.g. [parser k t], is related argument-wise, as by
                     [Rel], which does not unfold it: its unfoldings may only
                     be related by equations between its arguments that are
                     beyond the SMT solver, e.g. [parser_kind_prop #t k p ==>
                     parser_kind_prop #t' k' p], for types [t], [t'] equal by
                     unfolding. *)
                  let injective =
                    match (U.un_uinst head0).n with
                    | Tm_fvar fv -> Env.fv_has_attr g.tcenv fv PC.unifier_hint_injective_lid
                    | _ -> false
                  in
                  if (abs_args && rel = EQUALITY) || injective
                  then handle_with (argwise ()) (fun _ -> unfolded ())
                  else either_guard unfolded argwise
                | None -> compare_head_and_args ())
          )
          else compare_head_and_args ()
        )

      | Tm_abs {b=b0; body=body0}, Tm_abs {b=b1; body=body1} ->
        check_relation g EQUALITY b0.binder_bv.sort b1.binder_bv.sort;!
        check_bqual b0.binder_qual b1.binder_qual;!
        check_positivity_qual EQUALITY b0.binder_positivity b1.binder_positivity;!
        let! u = universe_of_well_typed_term g b0.binder_bv.sort in
        let g0 = g in
        let g, b0, body0 = open_term g b0 body0 in
        let body1 = Subst.subst [DB(0, b0.binder_bv)] body1 in
        with_binders g0 [b0] [u]
          (check_relation g EQUALITY body0 body1)

      | Tm_arrow {b=x0; comp=c0}, Tm_arrow {b=x1; comp=c1} ->
        with_context "subtype arrow" None (fun _ ->
          let! _ = check_bqual x0.binder_qual x1.binder_qual in
          check_positivity_qual rel x0.binder_positivity x1.binder_positivity;!
          (* The domains are related (contravariantly) in [g]: they do not
             mention the bound variable. *)
          let rel_arg =
            match rel with
            | EQUALITY -> EQUALITY
            | _ -> SUBTYPING None
          in
          check_relation g rel_arg x1.binder_bv.sort x0.binder_bv.sort ;!
          let! u1 = universe_of_well_typed_term g x1.binder_bv.sort in
          let g_x1, x1, c1 = open_comp g x1 c1 in
          let c0 = Subst.subst_comp [DB(0, x1.binder_bv)] c0 in
          with_binder_unrefined g x1 u1 (
            let rel_comp =
              match rel with
              | EQUALITY -> EQUALITY
              | SUBTYPING e ->
                SUBTYPING
                  (if U.is_pure_or_ghost_comp c0
                   then match e with
                        | None -> None
                        | Some (e, _) ->
                          (* Beta-reduced; the facts about [e]'s subterms
                             are not about the result's. *)
                          match (Subst.compress e).n with
                          | Tm_abs {body} ->
                            Some (Subst.subst [DB(0, x1.binder_bv)] body, no_facts_l ())
                          | _ ->
                            Some (S.mk_Tm_app e (snd (U.args_of_binders [x1])) R.dummyRange, no_facts_l ())
                   else None)
            in
            with_context "check_subcomp" None (fun _ ->
              check_relation_comp g_x1 rel_comp c0 c1
            )
          )
        )

      | Tm_match {scrutinee=e0;brs=brs0}, Tm_match {scrutinee=e1;brs=brs1} ->
        let relate_branch br0 br1 (_:unit)
          : ML (result unit)
          = match br0, br1 with
            | (p0, None, body0), (p1, None, body1) ->
              if not (S.eq_pat p0 p1)
              then fail_str "patterns not equal"
              else begin
                let g', (p0, _, body0), (p1, _, body1) = open_branches_eq_pat g (p0, None, body0) (p1, None, body1) in
                match PatternUtils.raw_pat_as_exp g.tcenv p0 with
                | Some (pe, bvs0) ->
                  let bs0 = List.map S.mk_binder bvs0 in
                  (* The universes of the binders: as the matches are
                     well-typed, so are their sorts, which are not re-checked
                     (as in the other rules, e.g. for [Tm_abs]); re-checking
                     them could need a guard, e.g. when the branches differ
                     only in the names of their pattern variables. *)
                  let! us = universes_of_well_typed_binders g bs0 in
                  (* The bodies are related knowing which branch is taken,
                     e.g. [y:t{x == Unknown u}] when relating
                     [dsum_type_of_unknown_tag s] to [t]. *)
                  let! sc_eq =
                    match! type_of_for_hypothesis g e0 with
                    | None -> return None
                    | Some (_, t_sc) ->
                      let! u_sc = quietly (universe_of_well_typed_term g t_sc) in
                      return (Some (U.mk_eq2 u_sc t_sc e0 pe))
                  in
                  let g'', hyp =
                    match sc_eq with
                    | None -> g', U.t_true
                    | Some h -> push_hypothesis g' h, h
                  in
                  with_context "relate_branch" None (fun _ ->
                    with_binders g bs0 us
                      (weaken_branch g' hyp (check_relation g'' rel body0 body1)))
                | _ -> fail_str "raw_pat_as_exp failed in check_equality match rule"
             end
            | _ -> fail_str "Core does not support branches with when"
        in
        handle_with
          (check_relation g EQUALITY e0 e1 ;!
           iter2 brs0 brs1 relate_branch ())
          (fun _ -> fallback t0 t1)

      | _ -> fallback t0 t1

and check_relation (g:env) (rel:relation) (t0 t1:typ)
  : ML (result unit)
  = (* With [use_eq_strict] (the [no_subtyping] attribute), there is no
       subtyping: the types must be equal. *)
    let rel = if g.tcenv.use_eq_strict then EQUALITY else rel in
    if !dbg
    then (
      fun ctx cache ->
        Format.print3 "check_relation (%s, %s, %s) {\n"
                    (show t0)
                    (show rel)
                    (show t1);
        let res = with_relation_failure_memo g rel t0 t1 (check_relation' g rel t0 t1) ctx cache in
        match res with
        | Error err ->
          Format.print4 "} check_relation (%s, %s, %s) failed with %s\n"
            (show t0) (show rel) (show t1) (show err);
          Error err
        | Success ((_, g), cache) ->
          Format.print4 "} check_relation  (%s, %s, %s) succeeded with guard %s\n"
            (show t0) (show rel) (show t1) (show g);
          res
    )
    else (
      with_relation_failure_memo g rel t0 t1 (check_relation' g rel t0 t1)
    )

and check_relation_args (g:env) rel (a0 a1:args)
  : ML (result unit)
  = if List.length a0 = List.length a1
    then iter2 a0 a1
         (fun (t0, q0) (t1, q1) _ ->
            check_aqual q0 q1;!
            check_relation g rel t0 t1)
         ()
    else fail_str "Unequal number of arguments"

and check_relation_comp (g:env) rel (c0 c1:comp)
  : ML (result unit)
  = let e0, t0 = comp_as_eff_and_type c0 in
    let e1, t1 = comp_as_eff_and_type c1 in
    match e0, e1 with
    | ETot, _
    | EGhost, EGhost ->
      (* A total computation may be used at any effect. For EQUALITY this is
         not quite right when [e1] is not [ETot], but relating two arrows whose
         comps differ only by an admissible sub-effect is what every caller of
         EQUALITY on comps has always relied on. *)
      check_relation g rel t0 t1

    | EGhost, ETot ->
      if non_informative g t1
      then check_relation g rel t0 t1
      else fail_str "Expected a Total computation, but got Ghost"

    | _ ->
      let ok =
        match rel with
        | EQUALITY -> eff_eq e0 e1
        | SUBTYPING _ -> sub_eff g e0 e1
      in
      if ok
      then (
        (* The result of an effectful computation is not a term we may put in
           a formula, so relate the result types without a witness. *)
        let rel =
          match rel with
          | EQUALITY -> EQUALITY
          | SUBTYPING _ -> SUBTYPING None
        in
        check_relation g rel t0 t1
      )
      else
        fail [
          text "Subcomp failed: computation with effect" ^/^ fquotes (pp (eff_to_lid e0))
          ^/^ text "cannot be used at effect" ^/^ fquotes (pp (eff_to_lid e1))
        ]

and check_subtype (g:env) (e:option witness) (t0 t1:typ)
: ML (result _)
  = let chk : result unit = fun ctx cache ->
      Profiling.profile
        (fun () ->
          let rel = SUBTYPING e in
          with_context (if ctx.no_guard then "check_subtype(no_guard)" else "check_subtype")
                       (Some (CtxRel t0 rel t1))
            (fun _ -> check_relation g rel t0 t1)
            ctx cache)
        None
        "FStarC.TypeChecker.Core.check_subtype"
    in
    match e with
    | Some (tm, _) -> label_subtyping g tm t0 t1 chk
    | None -> chk

(** Checking terms: G |- e : t | p, memoized (see [Core.Cache]). [check]
    and [check_f] are the entry points; [do_check] has the typing rules. *)

and memo_check (g:env) (e:term)
  : ML (result (eff & typ & facts))
  = let key = cache_key e in
    let e = key in
    let check_then_memo g e =
      with_guard (do_check_and_promote g e)
      (function
      | Inl (res, guard) ->
        insert g key (res, guard);!
        return_with_guard res guard

      | Inr err ->
        fail_propagate err)
    in
    if not g.should_read_cache
    then check_then_memo g e
    else (
      with_guard (lookup g key)
      (function
      | Inr _ ->
        check_then_memo g e
      | Inl (et, None) -> //cache hit; great, just return
        return et
      | Inl (et, pre) -> ( //cache hit with a guard
        failwith "Impossible"
      )
    ))

and check' (msg:string) (g:env) (e:term)
  : ML (result (eff & typ & facts))
  = with_context msg (Some (CtxTerm e)) (fun _ -> memo_check g e)

(* The effect and type of [e]. *)
and check (msg:string) (g:env) (e:term)
  : ML (result (eff & typ))
  = let! eff, t, _ = check_f msg g e in
    return (eff, t)

(* Also returning the facts about [e]. *)
and check_f (msg:string) (g:env) (e:term)
  : ML (result (eff & typ & facts))
  = if !dbg
    then (
      fun ctx cache -> 
        Format.print2 "{About to check %s %s\n" msg (show e);
        let res = check' msg g e ctx cache in
        match res with
        | Error err -> Error err
        | Success (((eff, typ, _), guard), cache) ->
          Format.print3 "Checked %s at type %s with guard %s}\n"
            (show e)
            (show typ)
            (show guard);
          res
    )
    else check' msg g e

and do_check_and_promote (g:env) (e:term)
  : ML (result (eff & typ & facts))
  = let! (eff, t, sf) = do_check g e in
    let eff =
      match eff with
      | EGhost -> if non_informative g t then ETot else EGhost
      | _ -> eff in
    return (eff, t, mk_facts g e eff t sf)

(* The type of [e], if it can be found, for stating a hypothesis about [e]:
   the guard of [e]'s typing is dropped, so the type may only be used in a
   hypothesis that holds whatever the guard, e.g. [e == p] on a branch where
   [e] matches [p]. The cache is kept only when there was no guard: its
   entries claim their guards have been emitted. *)
and type_of_for_hypothesis (g:env) (e:term)
  : ML (result (option (eff & typ)))
  = fun ctx cache ->
      match check "checked term" g e ctx cache with
      | Success ((et, None), cache') -> Success ((Some et, None), cache')
      | Success ((et, Some _), _) -> Success ((Some et, None), cache)
      | Error _ -> Success ((None, None), cache)

(*  G |- e : Tot t | pre, also returning the facts about the subterms of [e] *)
and do_check (g:env) (e:term)
  : ML (result (eff & typ & sub_facts)) =
  let e = Subst.compress e in
  match e.n with
  | Tm_lazy ({lkind=Lazy_embedding _}) ->
    do_check g (U.unlazy e)

  | Tm_lazy i ->
    no_sub (return (ETot, i.ltyp))

  | Tm_meta {tm=t; meta=Meta_monadic (m, a)}
      when (match (fst (U.head_and_args_full t)).n with
            | Tm_constant (FStarC.Const.Const_reflect _) -> true
            | _ -> false) ->
    (* [reflect e], as elaborated by TcTerm: [e] is the representation of
       a computation in [m] returning an [a]. *)
    let _, args = U.head_and_args_full t in
    (match args with
     | [(e, _)] ->
       let! _, t_a = check "reflect result type" g a in
       let! u_a = is_type g t_a in
       let! eff_e, t_e, fe = check_f "reflect argument" g e in
       if not (ETot? eff_e) then fail_str "Expected a total argument to reflect" else (
       let repr = Env.reify_comp g.tcenv (mk_comp_of_eff m a) u_a in
       check_subtype g (Some (e, fe.f_sub)) t_e repr ;!
       return (EEff m, a, { no_sub_facts () with s_sub = fe.f_term }))
     | _ -> fail_str "Ill-applied reflect")

  | Tm_meta {tm=t} ->
    let! eff, t, f = memo_check g t in
    return (eff, t, inner_facts f)

  | Tm_quoted (_, qi) ->
    no_sub (match qi.qkind with
     | Quote_static ->
       (* A static quotation is a [term], as long as its antiquotations are *)
       let rec aux (aqs:list term) : ML (result unit) =
         match aqs with
         | [] -> return ()
         | aq::aqs ->
           let! eff_aq, t_aq, faq = check_f "antiquotation" g aq in
           if not (ETot? eff_aq) then fail_str "Expected a total antiquotation" else (
           check_subtype g (Some (aq, faq.f_sub)) t_aq S.t_term ;!
           aux aqs)
       in
       aux (snd qi.antiquotations) ;!
       return (ETot, S.t_term)
     | Quote_dynamic ->
       (* The quoted term is only elaborated (laxly), not checked, by TcTerm *)
       return (EEff PC.effect_TAC_lid, S.t_term))

  | Tm_uvar (uv, s) ->
    no_sub (return (ETot, Subst.subst' s (U.ctx_uvar_typ uv)))

  | Tm_name x ->
    no_sub begin
    match Env.try_lookup_bv g.tcenv x with
    | None ->
      fail_str (Format.fmt1 "Variable not found: %s" (show x))
    | Some (t, _) ->
      (* As [Env.lookup_bv]: the type of an occurrence is used at the
         occurrence, e.g. the refinement of a recursive function's argument
         that proves termination is reported at the recursive call. *)
      return (ETot, Subst.set_use_range (S.range_of_bv x) t)
    end

  | Tm_fvar f ->
    no_sub begin
    match Env.try_lookup_lid g.tcenv f.fv_name with
    | Some (([], t), _) ->
      return (ETot, t)

    | _ -> //no implicit universe instantiation allowed
      fail_str "Missing universes instantiation"
    end

  | Tm_uinst ({n=Tm_fvar f}, us) ->
    no_sub begin
    match Env.try_lookup_and_inst_lid g.tcenv us f.fv_name with
    | None ->
      fail_str (Format.fmt1 "Top-level name not found: %s" (Ident.string_of_lid f.fv_name))

    | Some (t, _) ->
      return (ETot, t)
    end

  | Tm_constant c ->
    no_sub begin
    let open FStarC.Const in
    match c with
    | Const_range_of
    | Const_set_range_of
    | Const_reify _
    | Const_reflect _ ->
      fail_str "Unhandled constant"

    | _ ->
      let t = UniverseOf.tc_constant g.tcenv e.pos c in
      return (ETot, t)
    end

  | Tm_type u ->
    no_sub (return (ETot, mk_type (U_succ u)))

  | Tm_refine {b=x; phi} ->
    no_sub begin
    let! _, t = check "refinement head" g x.sort in
    let! u = is_type g t in
    let g', x, phi = open_term g (S.mk_binder x) phi in
    with_binders g [x] [u] (
      let! _, t' = check "refinement formula" g' phi in
      is_prop g' t';!
      (* As in [TcTerm]: a refinement is typed [Type u], even when its sort
         is, say, an [eqtype]. *)
      return (ETot, mk_type u)
    )
    end

  | Tm_abs _ ->
    (* One n-ary node at a time, as [TcTerm] does: [abs_formals_ln] would also
       look through ascriptions on the body, and so give the function a type
       with a longer arrow spine than the one the user wrote. The SMT encoding
       of a top-level definition depends on that spine. *)
    let xs, body, _ = U.abs_one_group_ln e in
    let g', xs, body = open_term_binders g xs body in
    let! us = with_context "abs binders" None (fun _ -> check_binders g xs) in
    (* A body ascribed with a computation type, e.g. [Lemma ... [SMTPat ...]],
       gives the function that computation type as written, flags,
       decreases clause and all: they are part of the function's type (the
       SMT encoding of a lemma depends on them), not just its effect. *)
    let rec ascribed_comp (t:term) : ML (option comp) =
      match (Subst.compress t).n with
      | Tm_ascribed {asc=(Inr c, _, _)} -> Some c
      | Tm_meta {tm; meta=Meta_pattern _}
      | Tm_meta {tm; meta=Meta_named _}
      | Tm_meta {tm; meta=Meta_labeled _}
      | Tm_meta {tm; meta=Meta_desugared _} -> ascribed_comp tm
      | _ -> None
    in
    with_binders g xs us (
      let! t = check "abs body" g' body in
      let c =
        match ascribed_comp body with
        | Some c -> c
        | None -> as_comp g t
      in
      return (ETot, U.arrow xs c, no_tail_facts ())
    )

  | Tm_arrow _ ->
    no_sub begin
    let xs, c = U.arrow_formals_comp_ln_strict e in
    let g', xs, c = open_comp_binders g xs c in
    let! us = with_context "arrow binders" None (fun _ -> check_binders g xs) in
    with_binders g xs us (
      let! u = with_context "arrow comp" None (fun _ -> check_comp g' c) in
      return (ETot, mk_type (S.U_max (u::us)))
    )
    end

  | Tm_app _ -> (
    (* [deps] are the (pure) arguments so far that the rest of the arrow
       depends on: the formal type of a later argument mentions them, and
       relating it to the actual type may need what their types say about
       them (e.g. [length (f xs) == length xs] to relate
       [list (swap (length xs))] and [list (swap (length (f xs)))]). TcTerm
       makes those facts available by binding every argument to a name of its
       type. *)
    (* [fs] are the facts about the arguments so far. *)
    let rec check_app_arg (st:(eff & typ & list (term & Thunk.t (list term)) & list (Thunk.t (list term)))) (a:arg)
      : ML (result (eff & typ & list (term & Thunk.t (list term)) & list (Thunk.t (list term)))) =
      let eff_hd, t_hd, deps, fs = st in
      let arg, arg_qual = a in
      let! x, eff_arr, t' = is_arrow g t_hd in
      let with_deps (#a:Type) (f:unit -> ML (result a)) : ML (result a) =
        match deps with
        | [] -> f ()
        | _ ->
          with_guard (f ()) (function
            | Inr err -> fail_propagate err
            | Inl (res, None) -> return res
            | Inl (res, Some form) ->
              match List.filter (fun (d, _) -> occurs_in d form) deps with
              | [] -> return_with_guard res (Some form)
              | deps ->
                match dedup_facts (List.collect (fun (_, f) -> Thunk.force f) deps) with
                | [] -> return_with_guard res (Some form)
                | facts ->
                  reemit_guard g (U.mk_imp (U.mk_conj_l facts) form) ;!
                  return res)
      in
      (* Every argument is checked against its formal, as by TcTerm, which
         typechecks an argument with the formal as its expected type. The
         formal is then pushed into a function, a [let] or a [match] (see
         [check_against_typ_synth]), so that, e.g., what the body of
         [fun _ -> (let w3 = ... in lemma (join w1 w3))] proves (in
         [introduce p ==> exists w3. q w3 with ...]) is in scope where the
         body's type is related to the formal's; and the branches of a match
         built by a tactic (e.g. Pulse's join of the postconditions of a
         conditional, [pts_to r (match b with true -> 0ul | false -> f x)])
         are each checked against the formal, rather than against the type of
         the first one, [x:U32.t{v x = 0}]. Other arguments have their type
         synthesized and related to the formal by subtyping, with the
         argument as the witness when it is pure. The obligations of the
         formal, e.g. a termination refinement, are about this argument:
         they are located at it, as by TcTerm. *)
      let formal = Subst.set_use_range arg.pos x.binder_bv.sort in
      let! eff_arg, _, f_arg =
        with_context "app arg" (Some (CtxTerm arg)) (fun _ ->
          with_deps (fun _ -> check_against_typ_synth g arg formal)) in
      (* A ghost argument for a non-informative formal, e.g. a total
         function for an [a -> GTot b], is total, as by TcTerm, which checks
         it against the formal. *)
      let eff_arg =
        match eff_arg with
        | EGhost when non_informative g x.binder_bv.sort -> ETot
        | _ -> eff_arg
      in
      let pure_arg = is_tot_or_ghost_eff eff_arg in
      with_context "app arg qual" None (fun _ -> check_arg_qual arg_qual x.binder_qual) ;!
      let! eff = join_eff_l g [eff_hd; eff_arr; eff_arg] in
      let dependent = mem x.binder_bv (FStarC.Syntax.Free.names t') in
      (* An effectful argument is not a term we may substitute into a type. *)
      if not pure_arg && dependent
      then fail [
             text "The type of this application depends on its argument"
             ^/^ fquotes (pp arg) ^/^ text "which has effect" ^/^ pp (eff_to_lid eff_arg)
           ]
      else
        (* What the type of a variable (or constant) says about it is
           already in scope, where the variable is bound. *)
        let atomic =
          match (Subst.compress (U.unmeta arg)).n with
          | Tm_name _ | Tm_fvar _ | Tm_uinst _ | Tm_constant _ -> true
          | _ -> false
        in
        return (eff, Subst.subst [NT(x.binder_bv, arg)] t',
                (if dependent && not atomic then deps @ [(arg, f_arg.f_term)] else deps),
                f_arg.f_term :: fs)
    in
    (* The facts about an application are those about its arguments. *)
    let check_app hd args =
       let! eff_hd, t = check "app head" g hd in
       let! eff, t, _, fs = fold check_app_arg (eff_hd, t, [], []) args in
       return (eff, t, { no_sub_facts () with s_sub = facts_concat (List.rev fs) })
    in
    let hd, args = U.head_and_args_full e in
    match (Subst.compress hd).n, args with
    | Tm_constant FStarC.Const.Const_range_of, [(e, None)] ->
      let! eff, _, fe = check_f "range_of argument" g e in
      return (eff, S.t_range, { no_sub_facts () with s_sub = fe.f_term })

    | Tm_constant FStarC.Const.Const_set_range_of, [(e, None); (r, None)] ->
      let! eff_r, t_r, fr = check_f "set_range_of range" g r in
      check_subtype g (if is_tot_or_ghost_eff eff_r then Some (r, fr.f_sub) else None) t_r S.t_range ;!
      let! eff_e, t_e, fe = check_f "set_range_of argument" g e in
      let! eff = join_eff g eff_r eff_e in
      return (eff, t_e, { no_sub_facts () with s_sub = facts_concat [fe.f_term; fr.f_term] })

    | Tm_constant (FStarC.Const.Const_reify _), [(e, _)] ->
      no_sub begin
      let! eff_e, t_e = check "reify argument" g e in
      (match eff_e with
       | EEff m when Env.is_user_reifiable_effect g.tcenv m ->
         let! u = universe_of_well_typed_term g t_e in
         let repr = Env.reify_comp g.tcenv (mk_comp_of_eff m t_e) u in
         let eff =
           if U.has_attribute (Env.get_effect_decl g.tcenv m).eff_attrs PC.primitive_extraction_attr then EGhost
           else if Env.is_total_effect g.tcenv m then ETot
           else EEff PC.primitive_div_lid
         in
         return (eff, repr)
       | _ -> fail_str "Expected a reifiable computation")
      end

    | Tm_constant FStarC.Const.Const_range_of, _
    | Tm_constant FStarC.Const.Const_set_range_of, _
    | Tm_constant (FStarC.Const.Const_reify _), _
    | Tm_constant (FStarC.Const.Const_reflect _), _ ->
      fail_str "Ill-applied or unexpected constant"

    | _, [(t1, _); (t2, _)] when VCUtil.short_circuit_head hd ->
      let! eff_hd, t_hd = check "app head" g hd in
      let! x, eff_arr1, s1 = is_arrow g t_hd in
      let! eff_arg1, t_t1, f1 = check_f "app arg" g t1 in
      with_context "operator arg1" None (fun _ -> check_subtype g (Some (t1, f1.f_sub)) t_t1 x.binder_bv.sort) ;!
      let s1 = Subst.subst [NT(x.binder_bv, t1)] s1 in
      let! y, eff_arr2, s2 = is_arrow g s1 in
      let guard_formula = VCUtil.short_circuit hd [(t1, None)] in
      let g' =
        match guard_formula with
        | CommonBase.Trivial -> g
        | CommonBase.NonTrivial gf -> push_hypothesis g gf
      in
      let! eff_arg2, t_t2, f2 = weaken_with_guard_formula g guard_formula (check_f "app arg" g' t2) in
      with_context "operator arg2" None (fun _ -> check_subtype g' (Some (t2, f2.f_sub)) t_t2 y.binder_bv.sort) ;!
      let! eff = join_eff_l g [eff_hd; eff_arr1; eff_arr2; eff_arg1; eff_arg2] in
      (* The facts about [t2] hold when it is evaluated. *)
      let f2 =
        match guard_formula with
        | CommonBase.Trivial -> f2.f_term
        | CommonBase.NonTrivial gf ->
          Thunk.map (fun (fs:list term) ->
            match fs with
            | [] -> []
            | _ -> [U.mk_imp gf (U.mk_conj_l fs)]) f2.f_term
      in
      return (eff, Subst.subst [NT(y.binder_bv, t2)] s2,
              { no_sub_facts () with s_sub = facts_concat [f1.f_term; f2] })

    | _, [(t, Some ({ aqual_implicit = true })); (tau, None)]
        when U.is_synth_by_tactic hd ->
      (* [synth_by_tactic #t tau] is left for Core by [TcTerm.tc_synth]
         when [t] is a proof goal: its tactic is to prove that goal, here,
         in the context in which Core checks it, as for [assert p by tau].
         A synthesis at any other type must have been run by the
         elaborator, and replaced by the tactic's result; the declaration
         of [synth_by_tactic] in the library gives no obligation for it. *)
      let! eff, ty, sf = check_app hd args in
      (match VCUtil.synth_proof_goal g.tcenv t with
       | Some p ->
         reemit_guard g (CommonBase.mk_by_tactic tau p) ;!
         return (eff, ty, sf)
       | None ->
         fail [
           text "This synthesis by a tactic was not run, and its type"
           ^/^ fquotes (pp t) ^/^ text "is not a proposition."
           ^/^ text "Synthesis is supported only in the definitions of top-level let-bindings."
         ])

    | _ -> check_app hd args
  )

  | Tm_ascribed {tm=e; asc=(Inl t, tac, eq)} ->
    let! _, t' = check "ascription type" g t in
    is_type g t';!
    check_ascription_tactic g tac;!
    let! eff, fe =
      with_ascription_tactic g tac (fun _ ->
        if eq
        then (
          (* [e $: t]: the type of [e] must be [t], not merely a subtype of it *)
          let! eff, te, fe = check_f "ascribed term" g e in
          with_context "ascription equality" None (fun _ -> check_relation g EQUALITY te t) ;!
          return (eff, fe)
        )
        else with_context "ascription subtyping" None (fun _ -> check_against_typ g e t)) in
    return (eff, t, inner_facts fe)

  | Tm_ascribed {tm=e; asc=(Inr c, tac, _)} ->
    let! _ = with_context "ascription comp" None (fun _ -> check_comp g c) in
    check_ascription_tactic g tac;!
    let! fe =
      with_ascription_tactic g tac (fun _ ->
        with_context "ascription subtyping (comp)" None (fun _ -> check_against_comp_f g e c)) in
    let eff, t = comp_as_eff_and_type c in
    return (eff, t, inner_facts fe)

  | Tm_let {lbs=(false, [lb]); body} ->
    check_let g lb body None

  | Tm_match {scrutinee=sc; ret_opt=None; brs=branches; rc_opt} ->
    (* Not built by the elaborator, which annotates every match: see
       [check_match]. *)
    let ret =
      match rc_opt with
      | Some ({ residual_typ = Some t }) -> Some (S.mk_binder (S.new_bv None S.tun), t, false)
      | _ -> None
    in
    check_match g e.pos sc ret branches

  | Tm_match {scrutinee=sc; ret_opt=Some (as_x, (Inl returns_ty, None, eq)); brs=branches} ->
    check_match g e.pos sc (Some (as_x, returns_ty, eq)) branches

  | Tm_match {scrutinee=sc; ret_opt=Some (as_x, (Inr c, None, eq)); brs; rc_opt} ->
    (* [returns C] is [returns t], where [t] is [C]'s result type, with an
       effect: computation types carry no specification beyond their effect
       and result type. *)
    let e' = { e with n = Tm_match {scrutinee=sc; ret_opt=Some (as_x, (Inl (U.comp_result c), None, eq)); brs; rc_opt} } in
    let! eff, t, sf = do_check g e' in
    let target = comp_eff c in
    let eff = match eff, target with
              | EGhost, ETot when non_informative g t -> ETot
              | _ -> eff in
    if not (sub_eff g eff target)
    then fail_effect_mismatch g e t eff (U.comp_result c) target
    else return (target, t, sf)

  | Tm_match _ ->
    fail_str "Match with a tactic handler on its returns annotation"

  | Tm_let {lbs=(true, lbs); body} ->
    let lbs, body = Subst.open_let_rec lbs body in
    let! us = check_letrec_types g lbs in
    let xs = letrec_binders lbs in
    let g' = push_binders g xs in
    with_binders g xs us (
      check_letrec_defs g None lbs us ;!
      let! eff, t, fb = check_f "let rec body" g' body in
      let fvs = FStarC.Syntax.Free.names t in
      if xs |> BU.for_some (fun x -> mem x.binder_bv fvs)
      then fail_str "Recursive name escapes its scope"
      else return (eff, t, letrec_facts xs us fb)
    )

  | _ ->
    fail_str (Format.fmt1 "Unexpected term: %s" (tag_of e))

(** Types, universes, binders and computation types *)

and is_prop (g:env) (t:term) : ML (result unit) =
  with_context "is_prop" (Some (CtxTerm t)) fun _ ->
    check_subtype g None t t_prop

and universe_of (g:env) (t:typ)
  : ML (result universe)
  = let! _, t = check "universe of" g t in
    is_type g t

and universe_of_well_typed_term (g:env) (t:typ)
  : ML (result universe)
  = (* Computed mostly syntactically (see [UniverseOf]); otherwise, by
       checking [t]. *)
    try
      let u = UniverseOf.universe_of UniverseOf.no_hooks g.tcenv t in
      return u
    with
    | _ -> universe_of g t

and universes_of_well_typed_binders (g_initial:env) (xs:binders)
  : ML (result (list universe))
  = let rec aux g xs : ML _ =
      match xs with
      | [] ->
        return []

      | x ::xs ->
        let! u = universe_of_well_typed_term g x.binder_bv.sort in
        with_binders g [x] [u] (
          let! us = aux (push_binder g x) xs in
          return (u::us)
        )
    in
    aux g_initial xs

and check_binders (g_initial:env) (xs:binders)
  : ML (result (list universe))
  = let rec aux g xs : ML _ =
      match xs with
      | [] ->
        return []

      | x ::xs ->
        let! _, t = check "binder sort" g x.binder_bv.sort in
        let! u = is_type g t in
        with_binders g [x] [u] (
          let g' = push_binder g x in
          let! us = aux g' xs in
          return (u::us)
        )
    in
    aux g_initial xs

//
// May be called with an effectful comp type, e.g. from within an arrow
// Caller should enforce Tot/GTot if needed
//
and check_comp (g:env) (c:comp)
  : ML (result universe)
  = match c.n with
    (* [Tot] and [GTot] are primitive: they have no signature to apply and no
       representation, so all there is to check is that the result is a type. *)
    | Comp ct when PC.is_tot_or_gtot_lid ct.effect_name ->
      let! _, t = check "(G)Tot comp result" g (U.comp_result c) in
      is_type g t
    | Comp ct ->
      (* A comp is its effect name applied to the result type. *)
      let u = g.tcenv.universe_of g.tcenv ct.result_typ in
      let effect_app_tm =
        let head = S.mk_Tm_uinst (S.fvar ct.effect_name None) [u] in
        S.mk_Tm_app head [as_arg ct.result_typ] ct.result_typ.pos in
      let! _, t = check "effectful comp" g effect_app_tm in
      with_context "comp fully applied" None (fun _ -> check_subtype g None t S.teff);!
      return (Env.effect_universe g.tcenv ct.effect_name u)

(** Checking against an expected type or computation type *)

(* Check [e] against the type [t], returning the effect of [e]. The expected
   type is pushed into [let]s and [match]es, as [TcTerm] does: a guard is then
   emitted where the relevant binders and path conditions are in scope, and
   with the pure result of an effectful computation as the witness. *)
and check_against_typ (g:env) (e:term) (t:typ)
  : ML (result (eff & facts))
  = let! eff, _, f = check_against_typ_synth g e t in
    return (eff, f)

(* As [check_against_typ], also returning the type synthesized for [e] when
   [e] is not one that the expected type is pushed into: that type is then
   related to [t] by subtyping, and may say more about [e] than [t] does. *)
and check_against_typ_synth (g:env) (e:term) (t:typ)
  : ML (result (eff & option typ & facts))
  = (* [e] checked against [x:t0{... /\ x == e /\ ...}] (e.g., a pure branch
       of a match against what [at_pattern] specializes its annotation to),
       with [e] total or ghost: the equation holds by reflexivity, so it is
       dropped and [e] is checked against the rest. The SMT solver may not
       prove it otherwise, e.g., when [e] contains a lambda, or a [let] that
       Core checks [e] by and the SMT encoding inlines. *)
    let drop_self_eq (t:typ) : ML (option typ) =
      match (Subst.compress t).n with
      | Tm_refine {b=x; phi} ->
        let x, phi = Subst.open_term_bv x phi in
        let rec conjuncts (phi:term) : ML (list term) =
          let hd, args = U.head_and_args_full (U.unmeta phi) in
          match (U.un_uinst hd).n, args with
          | Tm_fvar fv, [(p, None); (q, None)] when S.fv_eq_lid fv PC.and_lid ->
            conjuncts p @ conjuncts q
          | _ -> [phi]
        in
        let is_self_eq (phi:term) : ML bool =
          let hd, args = U.head_and_args_full (U.unmeta phi) in
          match (U.un_uinst hd).n, args with
          | Tm_fvar fv, [_; (l, None); (r, None)] when S.fv_eq_lid fv PC.eq2_lid ->
            (match (Subst.compress l).n with
             | Tm_name y ->
               S.bv_eq x y &&
               (TEQ.eq_tm g.tcenv r e = TEQ.Equal ||
                (* Syntactically, but for the effect annotations TcTerm
                   adds to some (but not all) copies of [e]. *)
                (let strip = Visit.visit_term false (fun t ->
                   match t.n with
                   | Tm_meta {tm; meta=Meta_monadic _}
                   | Tm_meta {tm; meta=Meta_monadic_lift _} -> tm
                   | _ -> t) in
                 U.term_eq (strip r) (strip e)))
             | _ -> false)
          | _ -> false
        in
        let cs = conjuncts phi in
        let rest = List.filter (fun c -> not (is_self_eq c)) cs in
        if List.length rest = List.length cs then None
        else if Nil? rest then Some x.sort
        else Some (U.refine x (U.mk_conj_l rest))
      | _ -> None
    in
    match drop_self_eq t with
    | Some t' ->
      let! eff, topt, f = check_against_typ_synth g e t' in
      if is_tot_or_ghost_eff eff then return (eff, topt, f)
      else check_against_typ_synth_aux g e t
    | None -> check_against_typ_synth_aux g e t

and check_against_typ_synth_aux (g:env) (e:term) (t:typ)
  : ML (result (eff & option typ & facts))
  = (* As in [do_check_and_promote]: e.g. [let z = ghost_f y in ()] is
       total, and may be composed with [Div]. *)
    let promote (ef:eff) : ML eff =
      match ef with
      | EGhost -> if non_informative g t then ETot else EGhost
      | _ -> ef
    in
    (* [e], checked against [t], is known to have type [t]. As [t] was
       pushed into [e], its type was not synthesized: what that type would
       have said about [e] beyond [t] is what the expression its [let]s end
       with establishes, e.g. the [squash p] of [lemma ()] in a branch
       [(lemma0 (); lemma ())] checked against [unit]. (Not so for an
       effectful [e], whose tail is not necessarily reached.) *)
    let checked (ef:eff) (sf:sub_facts) : ML (result (eff & option typ & facts)) =
      let ef = promote ef in
      let f = mk_facts g e ef t sf in
      let f =
        match sf.s_tail with
        | Some tl when is_tot_or_ghost_eff ef ->
          { f with f_term = Thunk.mk (fun () -> dedup_facts (Thunk.force f.f_term @ Thunk.force tl)) }
        | _ -> f
      in
      return (ef, None, f)
    in
    match (Subst.compress e).n with
    | Tm_let {lbs=(false, [lb]); body} ->
      let! eff, _, sf = check_let g lb body (Some t) in
      checked eff sf
    | Tm_match {scrutinee=sc; ret_opt=None; brs} ->
      (* An unannotated match (see [check_match]) is checked against [t]. *)
      let! eff, _, sf = check_match g e.pos sc (Some (S.mk_binder (S.new_bv None S.tun), t, false)) brs in
      checked eff sf
    | Tm_let {lbs=(true, lbs); body} ->
      (* The SMT encoding knows nothing of a local recursive function, so the
         expected type is related to the body's, rather than to the whole
         [let rec]. *)
      let lbs, body = Subst.open_let_rec lbs body in
      let! us = check_letrec_types g lbs in
      let xs = letrec_binders lbs in
      let! eff, topt, fb =
        with_binders g xs us (
          check_letrec_defs g None lbs us ;!
          check_against_typ_synth (push_binders g xs) body t) in
      let sf = letrec_facts xs us fb in
      (* What the body's own type says about it, which [letrec_facts] only
         states under an existential over the recursive names (e.g. the
         [nat] of [g n] in [let rec g (m:nat) : nat = ... in g n]), is said
         about the whole [let rec] instead, when that type does not mention
         them. *)
      (match topt with
       | Some te
           when (let fvs = FStarC.Syntax.Free.names te in
                 not (BU.for_some (fun (x:binder) -> mem x.binder_bv fvs) xs)) ->
         return (eff, topt, mk_facts g e eff te sf)
       | _ -> checked eff sf)
    | Tm_meta {tm}
        when (match (Subst.compress (U.unmeta tm)).n with
              | Tm_let _ | Tm_match _ -> true
              | _ -> false) ->
      let! eff, topt, f = check_against_typ_synth g tm t in
      (match topt with
       | None -> checked eff (inner_facts f)
       | Some te -> return (eff, topt, mk_facts g e eff te (inner_facts f)))
    | Tm_abs _ ->
      begin match abs_against_arrow g e t with
      | None -> check_against_typ_by_subtyping g e t
      | Some (xs, body, formals, c) ->
      (* A function checked against an arrow type has its body checked
         against the arrow's computation type, rather than having its type
         synthesized and then related to the arrow: the body, e.g. a [let]
         binding a local SMT lemma, may then scope over the goal. *)
      let _, xs, body = open_term_binders g xs body in
      let! us = with_context "abs binders" None (fun _ -> check_binders g xs) in
      let sub = List.map2 (fun (f:binder) (x:binder) -> NT(f.binder_bv, S.bv_to_name x.binder_bv)) formals xs in
      (* As by TcTerm (see [TcTerm.tc_abs_check_binders]), the annotation of
         each binder is related to its expected type in the scope of the
         binders before it only. [gi.at_top] is kept for closing the guard
         over the binders of the spine (see [with_binders]), not for
         checking anything else. *)
      let rec check_formals (gi:env) (formals:binders) (xs:binders) (us:universes) : ML (result unit) =
        let gi_ = { gi with at_top = false } in
        match formals, xs, us with
        | f::formals, x::xs, u::us ->
          label_guard gi_ x.binder_bv.sort.pos
            (fun () -> Errors.mkmsg "Type annotation on parameter incompatible with the expected type")
            (with_context "abs binder subtyping" None (fun _ ->
              check_subtype gi_ None (Subst.subst sub f.binder_bv.sort) x.binder_bv.sort)) ;!
          with_binders gi [x] [u]
            (check_formals { push_binder gi x with at_top = gi.at_top } formals xs us)
        | _ ->
          with_context "abs body" (Some (CtxTerm body)) (fun _ ->
            (* At the range of the abstraction, as TcTerm's
               [check_expected_effect], called by [tc_abs] in the
               abstraction's environment. *)
            label_postcondition gi_ e (check_against_comp gi_ body (Subst.subst_comp sub c)))
      in
      check_formals g formals xs us ;!
      return (ETot, None, no_facts ())
      end
    | _ -> check_against_typ_by_subtyping g e t

(* The tactic of an ascription [e <: t by tac] is a total [unit -> Tac unit]
   (see [TcTerm.tc_tactic]). *)
and check_ascription_tactic (g:env) (tac:option term) : ML (result unit) =
  match tac with
  | None -> return ()
  | Some tac ->
    let! eff_tac, _ =
      with_context "ascription tactic" (Some (CtxTerm tac)) (fun _ ->
        check_against_typ g tac (S.t_tac_of S.t_unit S.t_unit)) in
    if is_tot_or_ghost_eff eff_tac then return ()
    else fail_str "Expected the tactic of an ascription to be a total term"

and check_against_typ_by_subtyping (g:env) (e:term) (t:typ)
  : ML (result (eff & option typ & facts))
  = let! eff, te, f = check_f "checked term" g e in
    let w = if is_tot_or_ghost_eff eff then Some (e, f.f_sub) else None in
    let chk () = check_subtype g w te t in
    with_context "subtyping" (Some (CtxRel te (SUBTYPING w) t)) (fun _ ->
      (* [check_subtype] labels its guard when it has a witness. *)
      if Some? w then chk () else label_subtyping g e te t (chk ())) ;!
    return (eff, Some te, f)

(* Check [e] against [c], a
   computation type of any effect. *)
and check_against_comp (g:env) (e:term) (c:comp)
  : ML (result unit)
  = let! _ = check_against_comp_f g e c in
    return ()

(* Also returning the facts about [e]. *)
and check_against_comp_f (g:env) (e:term) (c:comp)
  : ML (result facts)
  = let reflected =
      let hd, args = U.head_and_args_full (U.unmeta e) in
      match (Subst.compress hd).n, args with
      | Tm_constant (FStarC.Const.Const_reflect l), [(e', _)]
          when I.lid_equals l (U.comp_effect_name c) ->
        Some e'
      | _ -> None
    in
    match reflected with
    | Some e' ->
      (* [M?.reflect e <: C], as elaborated by TcTerm for a reflection with
         an expected computation type [C] in [M]: [e] is a representation of
         [C]. *)
      let! u = universe_of_well_typed_term g (U.comp_result c) in
      let repr = Env.reify_comp g.tcenv c u in
      let! eff_e, fe' = check_against_typ g e' repr in
      if not (ETot? eff_e) then fail_str "Expected a total argument to reflect"
      else
        let eff, t = comp_as_eff_and_type c in
        return (mk_facts g e eff t { no_sub_facts () with s_sub = fe'.f_term })
    | None ->
    let target_eff, target_t = comp_as_eff_and_type c in
    let! eff, fe = check_against_typ g e target_t in
    let eff =
      match eff, target_eff with
      | EGhost, ETot when non_informative g target_t -> ETot
      | _ -> eff
    in
    if not (sub_eff g eff target_eff)
    then (
      let! _, t_e = handle_with (check "computed type" g e) (fun _ -> return (eff, target_t)) in
      fail_effect_mismatch g e t_e eff target_t target_eff
    )
    else return fe

(** let *)

(* A non-recursive [let x = e in body], with [body] checked against [expected]
   if given. In three steps: the definition ([check_let_def]); the body, with
   [x] bound at [let_binder_sort]; and the closing of the body's guard over
   [x] ([close_let_guard]) and, with no expected type, of its type
   ([let_result_typ]). *)
and check_let (g:env) (lb:letbinding) (body:term) (expected:option typ)
  : ML (result (eff & typ & sub_facts))
  = let Inl x0 = lb.lbname in
    let! eff_def, lbtyp, u, tdef, fdef = check_let_def g lb in
    let x0 = { x0 with sort = let_binder_sort g lbtyp tdef } in
    let g', x, body = open_term g (S.mk_binder x0) body in
    let! eff, t, fbody =
      close_let_guard g lb eff_def lbtyp tdef fdef x u (
        match expected with
        | Some t ->
          let! eff_body, fbody = check_against_typ g' body t in
          let! eff = join_eff g eff_def eff_body in
          return (eff, t, fbody)
        | None ->
          let! eff_body, t, fbody = check_f "let body" g' body in
          let! t = let_result_typ g g' lb.lbdef eff_def x u body eff_body t in
          let! eff = join_eff g eff_def eff_body in
          return (eff, t, fbody)) in
    return (eff, t, let_facts (is_tot_or_ghost_eff eff_def) lb.lbdef x.binder_bv u fdef fbody)

(* The definition [e] of a non-recursive [let]. Returns the effect of [e],
   the type [lbtyp] at which it is bound (its annotation, or else its own
   type), the universe of [lbtyp], the type synthesized for [e], if any, and
   the facts about [e].

   Without an annotation, the type of [e] is synthesized. With one, [e] is
   checked as follows, and then the annotation is checked to be a type:
   * A pure or ghost [e] is checked against it (see [check_against_typ]):
     the obligations of [e] meeting it are then where [e]'s own hypotheses
     are in scope, e.g. in [let f : t = (lemma (); f0) in body], [f0] meets
     [t] under the lemma. What [e] establishes beyond its annotation is
     stated in the VC of the body (see [close_let_guard]).
   * The result of an effectful [e] is described by its type only, which
     carries its postcondition, e.g. that [n >= 0] after
     [if n < 0 then fail ""]: that type is synthesized, and then related to
     the annotation.
   The effect the elaborator recorded in [lb.lbeff], that of the whole
   [let], bounds that of [e]: when it is pure or ghost, so is [e]. It only
   chooses between the two strategies, both of which are sound. *)
and check_let_def (g:env) (lb:letbinding)
  : ML (result (eff & typ & universe & option typ & facts))
  = if Tm_unknown? (Subst.compress lb.lbtyp).n
    then (
      (* A [let] appearing inside a *type* may still carry the annotation the
         desugarer left, i.e. none at all: not every producer of a term runs
         it through the elaborator first. *)
      let! eff, tdef, fdef = check_f "let definition" g lb.lbdef in
      (* The definition's type, which Core computed, is well-formed: only
         its universe is needed. *)
      let! u = quietly (universe_of_well_typed_term g tdef) in
      return (eff, tdef, u, Some tdef, fdef)
    )
    else (
      let pure =
        U.is_pure_or_ghost_effect lb.lbeff
        || Ident.lid_equals lb.lbeff PC.effect_Lemma_lid in
      let! eff, tdef, fdef =
        with_context "let definition" (Some (CtxTerm lb.lbdef)) (fun _ ->
          if pure
          then check_against_typ_synth g lb.lbdef lb.lbtyp
          else check_against_typ_by_subtyping g lb.lbdef lb.lbtyp) in
      (* The annotation is checked after the definition, whose guard then
         carries the well-formedness conditions the annotations inside it
         share with this one, e.g. [j < length a] for a local lemma
         [aux (j:nat{j < 16}) : Lemma (index a j == index b j)] whose body
         binds another such lemma: they are in scope of the goals of the
         body. Checked first, the annotation would emit them closed over its
         own binders, as a separate conjunct, and the identical guards of the
         body would then be dropped as cache hits (see [guard]). *)
      let! u = with_context "let type" (Some (CtxTerm lb.lbtyp)) (fun _ -> universe_of g lb.lbtyp) in
      return (eff, lb.lbtyp, u, tdef, fdef)
    )

(* Close the guard of [f], the body of a [let] binding [x] (of universe [u])
   to the definition [lb.lbdef], of effect [eff_def]. The variable of an
   effectful definition is merely a binder of its type. A pure or ghost
   definition is a term: the guard may assume its defining equation, or have
   it substituted for [x], and the facts [fdef] about it. *)
and close_let_guard (#a:Type) (g:env) (lb:letbinding) (eff_def:eff) (lbtyp:typ) (tdef:option typ)
                    (fdef:facts) (x:binder) (u:universe) (f:result a)
  : ML (result a)
  = if not (is_tot_or_ghost_eff eff_def) then with_binders g [x] [u] f else
    let annotated = not (Tm_unknown? (Subst.compress lb.lbtyp).n) in
    let smt_lemma_typ =
      if U.is_smt_lemma lbtyp then Some lbtyp
      else match tdef with
           | Some t when U.is_smt_lemma t -> Some t
           | _ -> None
    in
    (* As in [TcUtil.should_return], the defining equation of [x] is only
       worth stating if [x] may have more than one value, i.e. its type (or,
       for a function, its result type) is not [unit]-like, e.g. a local
       lemma; and if its definition is not irreducible. Such equations would
       only drag the definition, a lambda say, into the context of every
       later obligation. *)
    let def_eq_useful =
      let c = lbtyp |> U.arrow_formals_comp |> snd in
      U.is_pure_or_ghost_comp c
      && not (VCUtil.is_unit_like (N.unfold_whnf g.tcenv (U.comp_result c)))
      && (let head, _ = U.head_and_args_full lb.lbdef in
          match (U.un_uinst head).n with
          | Tm_fvar fv -> not (Env.is_irreducible g.tcenv (S.lid_of_fv fv))
          | _ -> true)
    in
    with_guard f (function
      | Inr err -> fail_propagate err
      | Inl (res, None) -> return res
      | Inl (res, Some form) ->
        (* A local lemma with SMT patterns, e.g.
           [let fwd x : Lemma (p x) [SMTPat (f x)] = ... in e], is available
           to the SMT solver in [e], as [TcTerm] does. *)
        let! form =
          match smt_lemma_typ with
          | None -> return form
          | Some lem_typ ->
            let! quant = handle_with (smt_lemma_as_forall g lem_typ) (fun _ -> return U.t_true) in
            return (U.mk_imp quant form)
        in
        (* [let unfold x = e] asks for [e] to be substituted into the VC, as
           [TcTerm] does. Without SMT, the guard must simplify to [True] as it
           stands: substituting the definition (which is equivalent to
           quantifying over [x] with its defining equation) lets it do so
           when it relates [x] to the definition itself. *)
        let inline_vc = U.has_attribute lb.lbattrs PC.inline_let_vc_attr || Options.no_smt () in
        (* Even when [x] does not occur in the guard, its defining equation
           is kept if it is useful, as TcTerm does: the definition may be
           there only to put a term into the VC, as a trigger, e.g.
           [introduce forall x y. q x y with let p = (x, y) in ()]. *)
        let x_free = def_eq_useful || mem x.binder_bv (FStarC.Syntax.Free.names form) in
        let quantified = x_free && not inline_vc in
        (* When [x] is quantified, what the definition's own type says about
           it is already said by [x]'s type: only the facts about its
           subterms remain. Otherwise they are stated about the definition
           itself, and, preferably, what its annotation says about it, as
           TcTerm assumes it: it may be stated differently than the
           definition's own type, even when the two are [term_eq], e.g. in
           the residual types of abstractions, which the SMT encoding of the
           abstractions depends on, as in
           [let _ : squash (p (fun x -> f x)) = lemma f in e]. *)
        let facts = Thunk.force (if quantified then fdef.f_sub else fdef.f_term) in
        let facts =
          if quantified || not annotated then facts
          else type_facts g true lb.lbdef lbtyp @ facts
        in
        (* When the annotation was pushed into the definition, its type was
           not synthesized: what it would have said about the definition
           beyond the annotation is stated here instead (see
           [let_binder_sort]), e.g. the [squash p] of
           [let _ : unit = (let x = e1 in lemma x) in body]. *)
        let facts =
          match tdef with
          | None -> facts @ Thunk.force fdef.f_tail
          | Some _ -> facts
        in
        let facts = dedup_facts facts in
        if !dbg_facts then Format.print2 "let facts for %s: %s\n" (show lb.lbdef) (show facts);
        let form =
          if inline_vc then Subst.subst [NT(x.binder_bv, lb.lbdef)] form
          else if not x_free then form
          else if def_eq_useful then close_with_definition x u lb.lbdef form
          else U.mk_forall u x.binder_bv form in
        let form = if Nil? facts then form else U.mk_imp (U.mk_conj_l facts) form in
        reemit_guard g form ;!
        return res)

(* The SMT lemma type [t] as a quantified formula with its patterns, as
   [U.smt_lemma_as_forall], with the universes of its binders computed here. *)
and smt_lemma_as_forall (g:env) (t:typ)
  : ML (result term)
  = match U.destruct_lemma_with_smt_patterns t with
    | None -> fail_str "not an SMT lemma"
    | Some (bs0, pre, post, patterns) ->
      let rec univs (g:env) (bs:binders) : ML (result (list universe)) =
        match bs with
        | [] -> return []
        | b::bs ->
          let! u = quietly (universe_of g b.binder_bv.sort) in
          let! us = univs (push_binders g [b]) bs in
          return (u::us)
      in
      let! us = univs g bs0 in
      let body = S.mk (Tm_meta {tm=U.mk_imp pre post;
                                meta=Meta_pattern (S.binders_to_names bs0, patterns)}) t.pos in
      return (List.fold_right2 (fun (b:binder) u out -> U.mk_forall u b.binder_bv out) bs0 us body)

(* The type of [let x = e in body], from the type [t] of [body], in which
   [x] may not escape. *)
and let_result_typ (g g':env) (e:term) (eff_def:eff) (x:binder) (u:universe)
                   (body:term) (eff_body:eff) (t:typ)
  : ML (result typ)
  = let x_in_t = mem x.binder_bv (FStarC.Syntax.Free.names t) in
    if is_tot_or_ghost_eff eff_def then (
      if x_in_t
      then return (Subst.subst [NT(x.binder_bv, e)] t)
      (* The definition's refinement is a fact about the rest of the
         computation; for a pure body, it is kept in the VC (see
         [close_let_guard]), but the result of an effectful body is only
         described by its type, so it is kept there, e.g.
         [let Some x = admit (); f () in ...] where [admit () : _:unit{False}]
         and [f] is effectful: the exhaustiveness check of the pattern relies
         on [False]. *)
      else if is_tot_or_ghost_eff eff_body then return t
      else
        let phi_x = U.refinement_hypothesis
                      (N.normalize_refinement N.whnf_steps g.tcenv x.binder_bv.sort)
                      (S.bv_to_name x.binder_bv) in
        if U.is_t_true phi_x then return t
        else
          let r = S.new_bv None t in
          return (U.refine r (U.mk_exists u x.binder_bv phi_x))
    )
    else (
      (* The result of an effectful definition cannot be substituted into
         the body's type. As in [TcUtil], [x] is instead closed
         existentially, over what the body's type says about it and, for a
         pure body, over the body itself (the value of the [let]), e.g.
         [let s = f x in C s y] has type [r:t{exists s. r == C s y}]. *)
      let x_in_body = mem x.binder_bv (FStarC.Syntax.Free.names body) in
      let eq_body = is_tot_or_ghost_eff eff_body in
      if not x_in_t && not eq_body then return t
      else if not x_in_t && not x_in_body then
        (* [body] is pure here ([eq_body], by the test above) and does not
           mention [x]: it is the value of the [let], if it returns at all,
           e.g. [let tok = f () in v] has value [v]. *)
        if U.is_unit (U.unrefine (N.unfold_whnf g'.tcenv t)) then return t
        else
          let r = S.new_bv None t in
          let! u_b = universe_of_well_typed_term g' t in
          return (U.refine r (U.mk_eq2 u_b t (S.bv_to_name r) body))
      else
        let tn = if x_in_t then N.normalize_refinement N.whnf_steps g'.tcenv t else t in
        let base = if x_in_t then U.unrefine tn else t in
        if mem x.binder_bv (FStarC.Syntax.Free.names base)
        then fail_str "Name escapes its scope"
        else
          let r = S.new_bv None base in
          let phi_t = if x_in_t then [U.refinement_hypothesis tn (S.bv_to_name r)] else [] in
          let! eq =
            if eq_body then
              let! u_b = universe_of_well_typed_term g' base in
              return [U.mk_eq2 u_b base (S.bv_to_name r) body]
            else return []
          in
          return (U.refine r (mk_exists_unrefined u x.binder_bv (U.mk_conj_l (phi_t @ eq))))
    )

(** let rec *)

and check_letrec_types (g:env) (lbs:list letbinding)
  : ML (result (list universe))
  = match lbs with
    | [] -> return []
    | lb::lbs ->
      let! u = with_context "let rec type" (Some (CtxTerm lb.lbtyp)) (fun _ -> universe_of g lb.lbtyp) in
      let! us = check_letrec_types g lbs in
      return (u::us)

(* Check the definitions of a nest of mutually recursive definitions, whose
   names (bound variables) and universes are already opened, and whose types
   are well-formed, at universes [us]. The guard may mention the names in the
   nest, at their declared types (the caller closes over them).

   A definition whose type is a total arrow must terminate. As in
   [TcTerm.tc_abs], its first [arity] binders are opened as the binders of its
   type, and every terminating name in the nest is then in scope at a type
   refined to only accept arguments that precede those binders (see
   [Termination.guard_letrecs]); the guard of the body is closed over those refined
   names right away, as it would be unsound to assume them at their declared
   types. Other definitions (and other names in the nest) are checked
   assuming the names at their declared types, as is sound for partial
   correctness. *)
and check_letrec_defs (g:env) (top:option (list subst_elt)) (lbs:list letbinding) (us:list universe)
  : ML (result unit)
  = (* [top]: for a top-level nest, maps its local names back to the
       top-level names; the guard of each body is stated with those,
       rather than quantified over the local names (see
       [check_top_level_letrec']).

        A total definition with [@@admit_termination] is not itself known to
       terminate, but, as in [TcTerm], its body must still respect the
       termination arguments of the other names in the nest. *)
    let lb_info (lb:letbinding) : ML (option (int & binders & comp)) =
      let bs, _, _ = U.abs_formals lb.lbdef in
      match bs with
      | [] -> None
      | _ ->
        let formals, c = N.get_n_binders_no_unrefine g.tcenv (List.length bs) lb.lbtyp in
        let arity = List.length formals in
        if arity = 0 then None
        else if U.comp_effect_name c |> Env.lookup_effect_quals g.tcenv |> List.contains TotalEffect
        then Some (arity, formals, c)
        else None
    in
    let admitted (lb:letbinding) = U.has_attribute lb.lbattrs PC.admit_termination_lid in
    let infos = List.map2 (fun lb u -> lb, u, lb_info lb) lbs us in
    let letrecs =
      infos |> List.collect (fun (lb, _, info) ->
        match info with
        | Some (arity, _, _) when not (admitted lb) -> [(lb.lbname, arity, lb.lbtyp, lb.lbunivs)]
        | _ -> [])
    in
    let g_plain = push_binders g (letrec_binders lbs) in
    let nonterminating =
      infos |> List.collect (fun (lb, u, info) ->
        if None? info || admitted lb then [S.mk_binder { Inl?.v lb.lbname with sort = lb.lbtyp }, u] else [])
    in
    let universe_of_name (l:lbname) : ML universe =
      match List.tryFind (fun (lb, _, _) -> S.bv_eq (Inl?.v lb.lbname) (Inl?.v l)) infos with
      | Some (_, u, _) -> u
      | None -> failwith "impossible: universe_of_name"
    in
    let check_one (lbi : letbinding & universe & option (int & binders & comp)) : ML (result unit) =
      let lb, _, info = lbi in
      match (Subst.compress lb.lbdef).n, info with
      | Tm_abs _, None ->
        with_context "let rec definition" (Some (CtxTerm lb.lbdef)) (fun _ ->
          check_against_comp g_plain lb.lbdef (S.mk_Total lb.lbtyp))

      | Tm_abs _, Some (arity, formals, c) ->
        let bs, body, rc = U.abs_formals lb.lbdef in
        let bs0, bs1 = List.splitAt arity bs in
        let body = if Nil? bs1 then body else U.abs bs1 body rc in
        let c = Subst.close_comp formals c in
        let formals = Subst.close_binders formals in
        (* As TcTerm, which checks the definition's own binders, name the
           formals as in the definition, not as in its type: they appear
           in the termination goals. *)
        let formals =
          List.map2 (fun (b:binder) (f:binder) ->
            if S.is_null_bv b.binder_bv then f
            else { f with binder_bv = { f.binder_bv with ppname = b.binder_bv.ppname } })
            bs0 formals
        in
        let g', formals, opening = open_binders g formals in
        let c = Subst.subst_comp opening c in
        let! ufs = with_context "let rec formals" None (fun _ -> check_binders g formals) in
        let sub = List.map2 (fun (b:binder) (f:binder) -> NT(b.binder_bv, S.bv_to_name f.binder_bv)) bs0 formals in
        (* Rename the definition's binders to the formals by closing and
           reopening, not by [sub], which would locate every occurrence at
           the binder. *)
        let body = Subst.subst opening (Subst.close bs0 body) in
        with_binders g formals ufs (
          let rec check_actuals (bs0:binders) (formals:binders) : ML (result unit) =
            match bs0, formals with
            | b::bs0, f::formals ->
              let sort = Subst.subst sub b.binder_bv.sort in
              let! _ = with_context "let rec binder" (Some (CtxTerm sort)) (fun _ -> universe_of g' sort) in
              with_context "let rec binder subtyping" None (fun _ ->
                check_subtype g' None f.binder_bv.sort sort) ;!
              check_actuals bs0 formals
            | _ -> return ()
          in
          check_actuals bs0 formals ;!
          (* The termination goals are labelled at the range of the
             environment: as in TcTerm, that of the definition, which
             includes the recursive calls. *)
          let refined =
            Termination.guard_letrecs true
              (Env.set_range { g'.tcenv with letrecs = letrecs } lb.lbdef.pos)
              formals c
          in
          (* The refined types are the formal types, already checked, with a
             [<<] refinement, whose universe instantiations [guard_letrecs]
             leaves as fresh unification variables. Check the refined types
             here, in context, which solves them. E.g., the decreases clause
             of a polymorphically recursive function may not be well-typed
             at the types of the recursive calls. *)
          let rec check_refined (ts:list typ) : ML (result unit) =
            match ts with
            | [] -> return ()
            | t::ts ->
              let! _ = with_context "let rec refined type" (Some (CtxTerm t))
                         (fun _ -> universe_of g' t) in
              check_refined ts
          in
          check_refined (List.map (fun (_, t, _) -> t) refined) ;!
          let refined =
            refined |> List.map (fun (l, t, _) ->
              let t = N.reduce_uvar_solutions g'.tcenv t in
              S.mk_binder { Inl?.v l with sort = t }, universe_of_name l)
          in
          let bs = List.map fst refined @ List.map fst nonterminating in
          let bus = List.map snd refined @ List.map snd nonterminating in
          let g'' = push_binders g' bs in
          let check_body () =
            with_context "let rec body" (Some (CtxTerm body)) (fun _ ->
              check_against_comp g'' body c)
          in
          match top with
          | None -> with_binders g' bs bus (check_body ())
          | Some back ->
            with_guard (check_body ()) (function
              | Inr err -> fail_propagate err
              | Inl (res, None) -> return res
              | Inl (res, Some form) ->
                reemit_guard g' (Subst.subst back form) ;!
                return res))

      | _ ->
        fail_str (Format.fmt1 "Only function literals may be defined recursively; got %s"
                    (show lb.lbdef))
    in
    let rec check_all infos : ML (result unit) =
      match infos with
      | [] -> return ()
      | i::is -> check_one i ;! check_all is
    in
    check_all infos

(** match: the scrutinee and the branches, patterns, and branch
    conditions *)

(* The rule for [match]. Every [match] the elaborator produces carries a
   [returns t] annotation (see [TcTerm.tc_match]), and is checked by this rule
   alone, with [ret = Some (as_x, t, eq)]:

     G |- sc : t_sc        G, as_x:t_sc |- t : Type
     for each branch [p_i -> b_i], under the path condition (no earlier
     pattern matched, and [p_i] does), with the variables of [p_i] in scope
     and [sc == p_i] assumed:
       G, bs_i, sc == p_i |- b_i : t[p_i/as_x]     (or [=] when [eq])
     the patterns are exhaustive
     -----------------------------------------------------------------------
     G |- match sc as as_x returns t with ... : t[sc/as_x]

   The branch is checked against the annotation at the pattern, rather than at
   the scrutinee, as in [TcTerm.tc_eqn]: e.g., a recursive function in it,
   applied to the pattern, reduces.

   Whatever the continuation of the match needs to know about it is in [t]: for
   an effectful match, the elaborator refines its result type with what each
   branch's type says about it (see [TcTerm.elaborated_match_returns]).

   Matches built by tactics and by Pulse may lack an annotation. They are
   checked by the same rule, with [t] the expected type, if any (see
   [check_against_typ_synth]), else the residual type recorded on the match, if
   any (see [do_check]), else (when [ret = None]) the type of the first
   branch, which must not mention the pattern's variables. *)
and check_match (g:env) (r:R.t) (sc:term) (ret:option (binder & typ & bool)) (branches:list branch)
  : ML (result (eff & typ & sub_facts))
  = let! eff_sc, t_sc = check "scrutinee" g sc in
    let! u_sc = universe_of_well_typed_term g t_sc in
    (* The annotation, opened, and its universe. *)
    let! ret =
      match ret with
      | None -> return None
      | Some (as_x, returns_ty, eq) ->
        let as_x = { as_x with binder_bv = { as_x.binder_bv with sort = t_sc } } in
        let g_as_x, as_x, returns_ty = open_term g as_x returns_ty in
        let dependent = mem as_x.binder_bv (FStarC.Syntax.Free.names returns_ty) in
        if dependent && not (is_tot_or_ghost_eff eff_sc)
        then fail [
               text "The return annotation of this match depends on its scrutinee"
               ^/^ fquotes (pp sc) ^/^ text "which has effect" ^/^ pp (eff_to_lid eff_sc)
             ]
        else
          let! _ =
            if dependent
            then with_binders g [as_x] [u_sc] (
                   let! _, k = check "return type" g_as_x returns_ty in
                   is_type g_as_x k)
            else (let! _, k = check "return type" g returns_ty in
                  is_type g k)
          in
          return (Some (as_x, returns_ty, eq))
    in
    (* The type the branch with pattern [p] (and expression [pat_exp]) is
       checked against, where [prev] are the patterns of the branches before
       it: [returns_ty], at [pat_exp].

       The annotation TcTerm elaborates for an effectful match (see
       [TcTerm.elaborated_match_returns]) is [x:t{match sc with | p_1 ->
       phi_1 ... | _ -> True}], with the patterns of the match itself. The
       branch is checked knowing that [p] is the first pattern to match [sc],
       so the formula is then that of its branch, [phi_i] (at the variables
       of [p]); and the branch is checked against [x:t{phi_i}]. That is not
       only simpler: for a pure branch [b_i], [phi_i] includes [x == b_i],
       which is then proved syntactically, whereas the SMT solver may not
       see two occurrences of [b_i] to be equal (e.g., when they contain
       lambdas), and no longer has to reduce the match. *)
    let at_pattern (g:env) (as_x:binder) (returns_ty:typ) (prev:list pat) (p:pat) (pat_exp:term) : ML typ =
      let t = Subst.subst [NT(as_x.binder_bv, pat_exp)] returns_ty in
      (* A renaming of the variables of [pf] to those of [p], if they are the
         same pattern. *)
      let rec pat_rename (pf p:pat) : ML (option (list subst_elt)) =
        match pf.v, p.v with
        | Pat_constant c1, Pat_constant c2 ->
          if FStarC.Const.eq_const c1 c2 then Some [] else None
        | Pat_var y, Pat_var z -> Some [NT(y, S.bv_to_name z)]
        | Pat_dot_term _, Pat_dot_term _ -> Some []
        | Pat_cons (f1, _, args1), Pat_cons (f2, _, args2) ->
          if S.fv_eq f1 f2 && List.length args1 = List.length args2
          then
            List.fold_left2
              (fun (acc:option (list subst_elt)) ((pf, b1):(pat & bool)) ((p, b2):(pat & bool)) ->
                match acc with
                | None -> None
                | Some s ->
                  if b1 <> b2 then None
                  else (match pat_rename pf p with
                        | None -> None
                        | Some s' -> Some (s @ s')))
              (Some []) args1 args2
          else None
        | _ -> None
      in
      let rec branch_formula (prev:list pat) (fbrs:list branch) : ML (option term) =
        match fbrs with
        | [] -> None
        | fbr :: fbrs ->
          let pf, wf, phif = Subst.open_branch fbr in
          if Some? wf then None
          else match pf.v with
          | Pat_var y -> Some (Subst.subst [NT(y, sc)] phif)
          | _ ->
            match prev with
            | q :: prev ->
              if Some? (pat_rename pf q) then branch_formula prev fbrs else None
            | [] ->
              (match pat_rename pf p with
               | Some s -> Some (Subst.subst s phif)
               | None -> None)
      in
      match (Subst.compress t).n with
      | Tm_refine {b=x; phi} ->
        let x, phi = Subst.open_term_bv x phi in
        (match (Subst.compress (U.unmeta phi)).n with
         | Tm_match {scrutinee=sf; brs=fbrs}
             when TEQ.eq_tm g.tcenv sf sc = TEQ.Equal ->
           (match branch_formula prev fbrs with
            | Some phi -> U.refine x phi
            | None -> t)
         | _ -> t)
      | _ -> t
    in
    (* The facts [fb] about the branch [b] taken under [cond], or else
       [this], the equation [pat_sc_eq] relating the scrutinee to the
       pattern binding [bs] (see [branch_conditions]). *)
    let branch_facts (bs:binders) (us:list universe) (cond this:term) (fb:facts)
      : ML (Thunk.t (list term)) =
      Thunk.mk (fun () ->
        (* Facts that do not mention the pattern variables hold whenever the
           branch is taken: stating them under [forall bs. sc == p ==> ...]
           would leave it to the SMT solver to find the [bs], e.g. for
           [eliminate exists]. *)
        let mentions_bs (f:term) : ML bool =
          let fvs = FStarC.Syntax.Free.names f in
          BU.for_some (fun (b:binder) -> mem b.binder_bv fvs) bs
        in
        let fb_free, fb_bound = List.partition (fun f -> not (mentions_bs f)) (Thunk.force fb.f_term) in
        (match fb_free with
         | [] -> []
         | _ -> [U.mk_imp cond (U.mk_conj_l fb_free)]) @
        (match fb_bound with
         | [] -> []
         | _ -> [mk_forall_l us bs (U.mk_imp this (U.mk_conj_l fb_bound))]))
    in
    let branches0 = branches in
    (* Returns the effect of the branches, the annotation (which the first
       branch provides when there is none), and the facts about the branches. *)
    let rec check_branches (prev:list pat) (path_condition:typ) (ret:option (binder & typ & bool))
                           (acc_eff:eff) (branches:list branch)
      : ML (result (eff & option (binder & typ & bool) & list (Thunk.t (list term))))
      = match branches with
        | [] ->
          if match_is_syntactically_exhaustive g t_sc branches0 then return (acc_eff, ret, []) else
          (match exhaustiveness_obligation r path_condition with
           | None -> return (acc_eff, ret, [])
           | Some phi -> guard g phi ;! return (acc_eff, ret, []))

        | (p, None, b) :: rest ->
          let _, (p, _, b) = open_branch g (p, None, b) in
          let! (bs, us) = with_context "check_pat" None (fun _ -> check_pat g p t_sc) in
          let! branch_condition = pattern_branch_condition g sc t_sc p in
          let pat_exp = PatternUtils.raw_pat_as_exp g.tcenv p |> Option.must |> fst in
          let pat_sc_eq = U.mk_eq2 u_sc t_sc sc pat_exp in
          let hyp, this, next_path_condition =
              branch_conditions path_condition branch_condition pat_sc_eq
          in
          let g_h = push_branch_hypothesis g hyp in
          let g'0 = push_binders g_h bs in
          let g' = push_hypothesis g'0 pat_sc_eq in
          let! eff_br, tbr, fb =
            weaken_branch g hyp
            (with_binders g_h bs us
              (weaken_branch g'0 pat_sc_eq
                 (with_context "branch" (Some (CtxTerm b)) (fun _ ->
                  match ret with
                  | None ->
                    let! eff_br, tbr, fb = check_f "branch" g' b in
                    check_no_escape bs tbr;!
                    return (eff_br, tbr, fb)
                  | Some (as_x, returns_ty, eq) ->
                    let expected = at_pattern g' as_x returns_ty prev p pat_exp in
                    if eq
                    then (
                      let! eff_br, tbr, fb = check_f "branch" g' b in
                      with_context "branch type equality" None (fun _ ->
                        check_relation g' EQUALITY tbr expected) ;!
                      return (eff_br, expected, fb)
                    )
                    else (
                      let! eff_br, fb = check_against_typ g' b expected in
                      return (eff_br, expected, fb)
                    ))))) in
          let ret =
            match ret with
            | None -> Some (S.mk_binder (S.new_bv None t_sc), tbr, false)
            | Some _ -> ret
          in
          let! acc_eff = join_eff g eff_br acc_eff in
          let fb = branch_facts bs us hyp this fb in
          (* Branches after a wildcard are dead code, checked, as by TcTerm,
             under the (false) path condition: their facts are not needed. *)
          let! eff, ret, more_fb = check_branches (prev @ [p]) next_path_condition ret acc_eff rest in
          let more_fb = match p.v with | Pat_var _ -> [] | _ -> more_fb in
          return (eff, ret, fb :: more_fb)

        | (_, Some w, _) :: _ ->
          with_context "when clause" (Some (CtxTerm w)) (fun _ ->
            fail_code Errors.Fatal_WhenClauseNotSupported
              (Errors.mkmsg "When clauses are not yet supported in --verify mode; they will be some day"))
    in
    let! eff_br, ret, fbs = check_branches [] U.t_true ret ETot branches in
    let! eff = join_eff g eff_sc eff_br in
    match ret with
    | None -> fail_str "could not compute a type for the match"
    | Some (as_x, returns_ty, _) ->
      return (eff, Subst.subst [NT(as_x.binder_bv, sc)] returns_ty,
              { s_sub = facts_concat fbs; s_tail = Some (no_facts_l ()) })

and check_pat (g:env) (p:pat) (t_sc:typ) : ML (result (binders & universes)) =
  let rec unrefine_tsc (t_sc:typ) : ML typ =
    let t = N.normalize_refinement N.whnf_steps g.tcenv (U.unmeta t_sc) |> U.unmeta in
    match (Subst.compress t).n with
    | Tm_refine {b} -> unrefine_tsc b.sort
    | _ -> t in

  match p.v with
  | Pat_constant c ->
    let e =
      match c with
      | FStarC.Const.Const_machine_int(repr, base, sw, w) ->
        FStarC.ToSyntax.ToSyntax.desugar_machine_integer g.tcenv.dsenv repr base (sw, w) p.p
      | _ ->
        mk (Tm_constant c) p.p in
    let! _, t_const = check "pat_const" g e in
    let! _ = with_context "check_pat constant" None (fun () -> check_subtype g (Some (e, no_facts_l ())) t_const (unrefine_tsc t_sc)) in
    return ([], [])

  | Pat_var bv ->
    let b = S.mk_binder {bv with sort=t_sc} in
    let! [u] = with_context "check_pat_binder" None (fun _ -> check_binders g [b]) in
    return ([b], [u])

  | Pat_cons (fv, usopt, pats) ->
    let us = if None? usopt then [] else usopt |> Option.must in

    let formals, t_pat =
      Env.lookup_and_inst_datacon g.tcenv us (S.lid_of_fv fv)
      |> U.arrow_formals in

    let dot_pats, rest_pats =
      let pats = pats |> List.map fst in
      pats |> BU.prefix_until (fun p -> match p.v with
                                    | Pat_dot_term _ -> false
                                    | _ -> true)
           |> Option.map (fun (dot_pats, pat, rest_pats) ->
                            dot_pats, (pat::rest_pats))
           |> Option.dflt (pats, []) in

    let dot_formals, rest_formals = List.splitAt (List.length dot_pats) formals in

    let! ss = fold2 (fun ss {binder_bv=f} p ->
      let expected_t = Subst.subst ss f.sort in
      let! pat_dot_t =
        match p.v with
        | Pat_dot_term (Some t) -> return t
        | _ -> fail_str "check_pat in core has unset dot pattern" in

      let! _, p_t = check "pat dot term" g pat_dot_t in
      let!_ = with_context "check_pat cons" None (fun _ -> check_subtype g (Some (pat_dot_t, no_facts_l ())) p_t expected_t) in

      return (ss@[NT (f, pat_dot_t)])) [] dot_formals dot_pats in

    let! _, ss, bs, us = fold2 (fun (g, ss, bs, us) {binder_bv=f} p ->
      let expected_t = Subst.subst ss f.sort in
      let! (bs_p, us_p) = with_binders g bs us (check_pat g p expected_t) in
      let p_e = PatternUtils.raw_pat_as_exp g.tcenv p |> Option.must |> fst in
      return (push_binders g bs_p,
              ss@[NT (f, p_e)],
              bs@bs_p,
              us@us_p)) (g, ss, [], []) rest_formals rest_pats in

    let t_pat = Subst.subst ss t_pat in

    let!_ = no_guard (check_scrutinee_pattern_type_compatible g (unrefine_tsc t_sc) t_pat) in

    return (bs, us)

  | _ -> fail_str "check_pat called with a dot pattern"

and check_scrutinee_pattern_type_compatible (g:env) (t_sc t_pat:typ)
  : ML (result precondition)
  = let open Env in
    let err (s:string) =
      fail [
        flow (break_ 1) [
          text "Scrutinee type";
          fquotes (pp t_sc);
          text "and pattern type";
          fquotes (pp t_pat);
          text "are not compatible because";
          text s;
        ]
      ]
    in

    let head_sc, args_sc = U.head_and_args_full t_sc in
    let head_pat, args_pat = U.head_and_args_full t_pat in

    let! (t_fv:fv) =
      match (Subst.compress head_sc).n, (Subst.compress head_pat).n with
      | Tm_fvar (fv_head), Tm_fvar (fv_pat)
        when Ident.lid_equals (lid_of_fv fv_head) (lid_of_fv fv_pat) -> return fv_head
      | Tm_uinst ({n=Tm_fvar (fv_head)}, us_head), Tm_uinst ({n=Tm_fvar (fv_pat)}, us_pat)
        when Ident.lid_equals (lid_of_fv fv_head) (lid_of_fv fv_pat) ->
        if UnivEq.teq_univs g.tcenv us_head us_pat
        then return fv_head
        else err "Incompatible universe instantiations"
      | _, _ -> err (Format.fmt2 "Head constructors(%s and %s) not fvar"
                      (tag_of head_sc)
                      (tag_of head_pat)) in

    (if Env.is_type_constructor g.tcenv (lid_of_fv t_fv)
     then return t_fv
     else err (Format.fmt1 "%s is not a type constructor" (show t_fv)));!

    (if List.length args_sc = List.length args_pat then return t_fv
     else err (Format.fmt2 "Number of arguments don't match (%s and %s)"
                          (show (List.length args_sc))
                          (show (List.length args_pat))));!

   let params_sc, params_pat =
     match Env.num_inductive_ty_params g.tcenv (S.lid_of_fv t_fv) with
     | None -> args_sc, args_pat
     | Some n -> fst (BU.first_N n args_sc), fst (BU.first_N n args_pat) in

  iter2 params_sc params_pat (fun (t_sc, _) (t_pat, _) _ ->
     check_relation g EQUALITY t_sc t_pat) () ;!

   // TODO: return equality of indices for the caller to weaken the guard with?

   return None

(* The condition under which [scrutinee] matches [pat]. It does not mention
   the variables of the pattern: those that the pattern's dot terms (e.g. the
   parameters of a constructor) mention are replaced by the corresponding
   projections of the scrutinee. *)
and pattern_branch_condition (g:env) (scrutinee:term) (t_sc:typ) (pat:pat)
  : ML (result (option term))
  = let! bc = pattern_branch_condition' g scrutinee (Thunk.mkv (Some t_sc)) pat in
    match bc with
    | None -> return None
    | Some bc ->
      let projs = pattern_var_projections g scrutinee (Thunk.mkv (Some t_sc)) pat in
      let sub =
        List.fold_left
          (fun (sub:list subst_elt) (x, t) -> sub @ [NT(x, Subst.subst sub t)])
          [] projs in
      return (Some (Subst.subst sub bc))

(* Each variable of [pat], as a projection of [scrutinee] (of type [t_sc],
   if known), in the order they are bound. *)
and pattern_var_projections (g:env) (scrutinee:term) (t_sc:Thunk.t (option typ)) (pat:pat)
  : ML (list (bv & term))
  = match pat.v with
    | Pat_var x -> [(x, scrutinee)]
    | Pat_cons (fv, us_opt, sub_pats) ->
      let type_args = inductive_type_args g t_sc fv in
      List.flatten (List.mapi (fun i (pi, _) ->
        match pi.v with
        | Pat_var _ | Pat_cons _ ->
          let proj, t_proj = pat_field_projection g scrutinee pat.p fv us_opt type_args sub_pats i in
          pattern_var_projections g proj t_proj pi
        | _ -> []) sub_pats)
    | _ -> []

and pattern_branch_condition' (g:env)
                             (scrutinee:term)
                             (t_sc:Thunk.t (option typ))
                             (pat:pat)
  : ML (result (option term))
  = match pat.v with
    | Pat_var _ ->
      return None
    | Pat_constant FStarC.Const.Const_unit ->
      (* [()] always matches *)
      return None
    | Pat_constant c ->
      let const_exp =
        match PatternUtils.raw_pat_as_exp g.tcenv pat with
        | None -> failwith "Impossible"
        | Some (e, _) -> e
      in
      let! _, t_const = check "constant pattern" g const_exp in
      return (Some (U.mk_decidable_eq t_const scrutinee const_exp))

    | Pat_cons(fv, us_opt, sub_pats) ->
      let wild_pat pos = S.withinfo (Pat_var (wild_bv S.tun pos)) pos in
      let mk_head_discriminator () =
        (* Dot patterns (the constructor's parameters) are kept, so that the
           discriminator is well-typed if it ends up in a type Core checks. *)
        let wild_sub_pat (s, b) =
          match s.v with
          | Pat_dot_term (Some _) -> (s, b)
          | _ -> (wild_pat s.p, b) in
        let pat = S.withinfo (Pat_cons(fv, us_opt, List.map wild_sub_pat sub_pats)) pat.p in
        let branch1 = (pat, None, U.exp_true_bool) in
        let branch2 = (S.withinfo (Pat_var (wild_bv S.tun pat.p)) pat.p, None, U.exp_false_bool) in
        S.mk (Tm_match {scrutinee; ret_opt=None; brs=[branch1; branch2]; rc_opt=None}) scrutinee.pos
      in
      let type_args = inductive_type_args g t_sc fv in
      let mk_ith_projector i = pat_field_projection g scrutinee pat.p fv us_opt type_args sub_pats i in
      let discrimination =
        let is_induc, datacons = Env.datacons_of_typ g.tcenv (Env.typ_of_datacon g.tcenv fv.fv_name) in
        (* Why the `not is_induc`? We may be checking an exception pattern. See issue #1535. *)
        if not is_induc || List.length datacons > 1
        then let discriminator = U.mk_discriminator fv.fv_name in
             match Env.try_lookup_lid g.tcenv discriminator with
             | None ->
               // We don't use the discriminator if we are typechecking it
               None
             | _ ->
               Some discriminator
        else None //single constructor inductives do not need a discriminator
      in
      (* The discriminator is applied to the scrutinee, as [TcTerm] builds
         branch conditions: the SMT encoding of a [match] on the scrutinee
         is a term of its own, about which the solver knows less, e.g. when
         the scrutinee is itself a projection, [TEq? b && Nat? b.t]. Its
         implicit arguments are the scrutinee type's parameters and indices;
         failing to find them, a [match] is used. *)
      let! discrimination =
        match discrimination with
        | None -> return None
        | Some discriminator ->
          let type_args =
            match type_args with
            | Some _ -> type_args
            | None ->
              match datacon_params_of_pat g fv sub_pats with
              | Some ts -> Some (us_opt, ts)
              | None -> None
          in
          let app =
            match type_args with
            | None -> None
            | Some (us, args) ->
              let d = S.fvar (I.set_lid_range discriminator scrutinee.pos) None in
              let d = match us with | Some us -> S.mk_Tm_uinst d us | None -> d in
              Some (S.mk_Tm_app d (List.map S.iarg args @ [S.as_arg scrutinee]) scrutinee.pos)
          in
          match app with
          | Some app -> return (Some app)
          | None -> return (Some (mk_head_discriminator ()))
      in
      let! sub_term_guards =
          mapi
          (fun i (pi, _) ->
            match pi.v with
            | Pat_dot_term _
            | Pat_var _ ->
              return None
            | _ ->
              let sub_term, t_sub_term = mk_ith_projector i in
              pattern_branch_condition' g sub_term t_sub_term pi)
          sub_pats
      in
      let guards = List.collect (function None -> [] | Some t -> [t]) (discrimination :: sub_term_guards) in
      match guards with
      | [] -> return None
      | guards -> return (Some (U.mk_and_l guards))

(*** The public API *)

//
// In case the expected type and effect are set,
//   they are returned as is
//
let check_term_top' g e topt (must_tot:bool)
  : ML (result (eff & typ))
  = let g = { initial_env g with at_top = Tm_abs? (Subst.compress (U.unascribe e)).n } in
    let! eff_te =
      match topt with
      | None -> check "top" g e
      | Some t ->
        let! eff, _ =
          with_context "top-level subtyping" None (fun _ ->
            check_against_typ ({ g with allow_universe_instantiation = true}) e t) in
        return (eff, t)
    in
    let eff_te =
      match eff_te with
      | EGhost, t when must_tot && non_informative g t -> ETot, t
      | _ -> eff_te
    in
    if must_tot && not (eff_eq (fst eff_te) ETot)
    then fail_effect_mismatch g e (snd eff_te) (fst eff_te) (snd eff_te) ETot
    else return eff_te

(* Check [e] against the computation type [c] (of any effect). *)
let check_term_at_comp' g e (c:comp)
  : ML (result (eff & typ))
  = let g = initial_env g in
    let target = comp_as_eff_and_type c in
    check_against_comp ({ g with allow_universe_instantiation = true}) e c ;!
    return target

(* Check a nest of top-level recursive definitions, with their universes
   opened and pushed in [g]. The top-level names are replaced by fresh
   variables, so that the nest is checked (and its guard closed) just as an
   inner let rec. *)
let check_top_level_letrec' g (lbs:list letbinding)
  : ML (result (eff & typ))
  = let g = initial_env g in
    let names =
      lbs |> List.map (fun lb ->
        let fv = Inr?.v lb.lbname in
        fv, S.gen_bv (Ident.string_of_id (Ident.ident_of_lid fv.fv_name)) (Some (S.range_of_fv fv)) lb.lbtyp)
    in
    let name_of (fv:fv) : ML (option bv) =
      match List.tryFind (fun (fv', _) -> S.fv_eq fv fv') names with
      | Some (_, x) -> Some x
      | None -> None
    in
    let replace (t:term) : ML term =
      t |> Syntax.Visit.visit_term false (fun t ->
        match t.n with
        (* Occurrences keep their ranges: the type of a name is used at
           its occurrence (see [lookup]). *)
        | Tm_fvar fv ->
          (match name_of fv with
           | Some x -> { t with n = Tm_name (S.set_range_of_bv x t.pos) }
           | None -> t)
        | Tm_uinst ({n=Tm_name x}, _) -> { t with n = Tm_name (S.set_range_of_bv x t.pos) }
        | _ -> t)
    in
    let lbs =
      List.map2 (fun lb (_, x) -> { lb with lbname = Inl x; lbdef = replace lb.lbdef }) lbs names
    in
    let! us = check_letrec_types g lbs in
    (* The guard mentions the names at their declared types: substitute the
       top-level names back, rather than quantifying over them, as they are
       in TcTerm's environment when it discharges the guard. *)
    let back : list subst_elt =
      List.map2 (fun (lb:letbinding) (fv, x) ->
        let t = S.fv_to_tm fv in
        let t = match lb.lbunivs with
                | [] -> t
                | us -> S.mk_Tm_uinst t (List.map U_name us) in
        NT (x, t)) lbs names
    in
    with_guard (check_letrec_defs g (Some back) lbs us) (function
      | Inr err -> fail_propagate err
      | Inl (_, None) -> return (ETot, S.t_unit)
      | Inl (_, Some form) ->
        reemit_guard g (Subst.subst back form) ;!
        return (ETot, S.t_unit))

(* The SMT encoding names a function literal after its body and its type,
   including the residual type of its body (see Bug1595). TcTerm gives a
   literal checked against an expected arrow the residual type of that arrow,
   e.g. [_:bool{_ == true <==> o x y}] for [fun x y -> f x y] passed as a
   [x:_ -> y:_ -> Pure bool True (fun z -> z == true <==> o x y)], and its
   unifier copies the literal as is into implicit arguments, e.g. the [p] of
   [Classical.forall_intro], where the same literal elsewhere has residual
   type [bool]: the two copies would be distinct terms to the SMT solver.
   (Core checks the elaboration as is, so nothing recomputes their residual
   types from their position.) In a guard, the residual types of
   function literals are only used for the typing axioms of their encodings,
   so they are weakened to their unrefined types: copies of a literal are
   then encoded alike. When the body, or the tail of its [let]s, is ascribed
   a refinement type (e.g., [fun y -> let _ = lem y in (y <: y:t{p y})]), the
   residual type is that of the literal itself, rather than of its position,
   and is kept: it is the same in all copies, including those in definitions,
   which are encoded as they are. *)
let unrefine_abs_residuals (t:term) : ML term =
  let rec ascribed_a_refinement (body:term) : ML bool =
    match (Subst.compress body).n with
    | Tm_ascribed {asc=(Inl t', _, _)} -> Tm_refine? (Subst.compress t').n
    | Tm_meta {tm} -> ascribed_a_refinement tm
    | Tm_let {lbs=(false, _); body} -> ascribed_a_refinement body
    | _ -> false
  in
  Visit.visit_term false (fun t ->
    match t.n with
    | Tm_abs ab when Some? ab.rc_opt && Some? (Some?.v ab.rc_opt).residual_typ ->
      let rc = Some?.v ab.rc_opt in
      let rt = Some?.v rc.residual_typ in
      if not (Tm_refine? (Subst.compress rt).n) || ascribed_a_refinement ab.body then t
      else { t with n = Tm_abs { ab with rc_opt = Some { rc with residual_typ = Some (U.unrefine rt) } } }
    | _ -> t) t

let simplify_steps =
    [Env.Beta;
     Env.UnfoldUntil delta_constant;
     Env.UnfoldQual ["unfold"];
     Env.UnfoldOnly [PC.pure_wp_monotonic_lid; PC.pure_wp_monotonic0_lid];
     Env.Simplify;
     Env.Primops;
     Env.NoFullNorm]

let check_term_top_gen (g:Env.env) (e:term) (topt:option typ) (simplify:bool) (f:result (eff & typ))
  : ML (__result ((eff & S.typ) & precondition))
  = if !dbg_Eq
    then Format.print1 "(%s) Entering core ... \n"
                   (show (get_goal_ctr()));

    if !dbg || !dbg_Top
    then (Format.print3 "(%s) Entering core with %s <: %s\n"
                   (show (get_goal_ctr()))
                   (show e) 
                   (show topt));
    reset_cache_stats();
    clear_relation_failures ();
    let ctx = { unfolding_ok = true; no_guard = false; error_context = [("Top", None)] } in
    let res =
      Profiling.profile
        (fun () -> f ctx initial_cache)
        None
        "FStarC.TypeChecker.Core.check_term_top"
    in
    if !dbg || !dbg_Top
    then Format.print2 "(%s) Core result = %s\n"
                   (show (get_goal_ctr()))
                   (show res);
    (
    let res =
      match res with
      | Success ((et, Some guard0), cache) ->
        // Options.push();
        // Options.set_option "debug" (Options.List [Options.String "Unfolding"]);
        let guard = unrefine_abs_residuals guard0 in
        let guard = if simplify then N.normalize simplify_steps g guard else guard in
        // Options.pop();
        if !dbg || !dbg_Top || !dbg_Exit
        then begin
          Format.print3 "(%s) Exiting core: Simplified guard from {{%s}} to {{%s}}\n"
            (show (get_goal_ctr()))
            (show guard0)
            (show guard);
          let guard_names = Syntax.Free.names guard |> elems in
          match List.tryFind (fun bv -> List.for_all (fun binding_env ->
            match binding_env with
            | Binding_var bv_env -> not (S.bv_eq bv_env bv)
            | _ -> true) g.gamma) guard_names with
          | Some bv ->
            Format.print1 "WARNING: %s is free in the core generated guard\n" (show (S.bv_to_name bv))
          | _ -> ()
        end;
        Success ((et, Some guard), cache)

      | Success _ ->
        if !dbg || !dbg_Top
        then Format.print1 "(%s) Exiting core (ok)\n"
                    (show (get_goal_ctr()));
        res

      | Error _ ->
        if !dbg || !dbg_Top
        then Format.print1 "(%s) Exiting core (failed)\n"
                       (show (get_goal_ctr()));
        res
    in
    if !dbg_Eq
    then (
      Format.print1 "THT Statistics { num_bindings = %s }\n" (show (HashTable.size table.table));
      let cs = report_cache_stats() in
      Format.print2 "Cache_stats { hits = %s; misses = %s }\n"
                     (show cs.hits)
                     (show cs.misses)
    );
    res
    )

let return_my_guard_and_tok_t (g:precondition) (cache:cache_t) : ML (option (typ & (unit -> ML unit))) =
    let tok = mk_token cache in
    match g with
    | None -> 
      commit_guard_core tok;
      None
    | Some guard ->
      Some (guard, (fun _ -> commit_guard_core tok))

let check_term_top g e topt (must_tot:bool)
  : ML (__result ((tot_or_ghost & S.typ) & precondition))
  = match check_term_top_gen g e topt true (check_term_top' g e topt must_tot) with
    | Success (((ETot, t), guard), cache) -> Success (((E_Total, t), guard), cache)
    | Success (((EGhost, t), guard), cache) -> Success (((E_Ghost, t), guard), cache)
    | Success (((EEff m, _), _), _) ->
      Error ({ unfolding_ok = true; no_guard = false; error_context = [("Top", None)] },
             [text "Expected a total or ghost term, but it has effect" ^/^ pp m], None)
    | Error err -> Error err

let check_term g e t must_tot =
  match check_term_top g e (Some t) must_tot with
  | Success ((_, g), cache) -> Inl <| return_my_guard_and_tok_t g cache
  | Error err -> Inr err

let check_term_at_type g e t =
  let must_tot = false in
  match check_term_top g e (Some t) must_tot with
  | Success (((eff, _), g), cache) -> Inl (eff, return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let compute_term_type g e =
  let must_tot = false in
  match check_term_top g e None must_tot with
  | Success (((eff, ty), g), cache) -> Inl (eff, ty, return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let check_term_at_comp g e c =
  match check_term_top_gen g e (Some (U.comp_result c)) false (check_term_at_comp' g e c) with
  | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let check_top_level_letrec g lbs =
  match check_term_top_gen g S.unit_const None false (check_top_level_letrec' g lbs) with
  | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let compute_term_comp g e topt check_t =
  let f : result (eff & typ) =
    match topt with
    | None -> check_term_top' g e None false
    | Some _ when not check_t -> check_term_top' g e topt false
    | Some t ->
      fun ctx cache ->
        let g0 = initial_env g in
        (let! _ = with_context "expected type" (Some (CtxTerm t)) (fun _ -> universe_of g0 t) in
         check_term_top' g e topt false) ctx cache
  in
  match check_term_top_gen g e topt false f with
  | Success ((et, g), cache) ->
    let c =
      match et with
      | ETot, t -> S.mk_Total t
      | EGhost, t -> S.mk_GTotal t
      | EEff m, t -> mk_comp_of_eff m t
    in
    Inl (c, return_my_guard_and_tok_t g cache)
  | Error err -> Inr err

let open_binders_in_term (env:Env.env) (bs:binders) (t:term) =
  let g = initial_env env in
  let g', bs, t = open_term_binders g bs t in
  g'.tcenv, bs, t

let open_binders_in_comp (env:Env.env) (bs:binders) (c:comp) =
  let g = initial_env env in
  let g', bs, c = open_comp_binders g bs c in
  g'.tcenv, bs, c

let check_term_equality guard_ok unfolding_ok g t0 t1
  = let g = initial_env g in
    if !dbg_Top then
       Format.print4 "Entering check_term_equality with %s and %s (guard_ok=%s; unfolding_ok=%s) {\n"
         (show t0) (show t1) (show guard_ok) (show unfolding_ok);
    clear_relation_failures ();
    let ctx = { unfolding_ok = unfolding_ok; no_guard = not guard_ok; error_context = [("Eq", None)] } in
    let r = guard_if_trivial g (check_relation g EQUALITY t0 t1) ctx initial_cache in
    if !dbg_Top then
       Format.print3 "} Exiting check_term_equality (%s, %s). Result = %s.\n" (show t0) (show t1) (show r);
    let r =
      match r with
      | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
      | Error err -> Inr err
    in
    r

let check_term_subtyping guard_ok unfolding_ok g t0 t1
  = let g = initial_env g in
    clear_relation_failures ();
    let ctx = { unfolding_ok = unfolding_ok; no_guard = not guard_ok; error_context = [("Subtyping", None)] } in
    match guard_if_trivial g (check_relation g (SUBTYPING None) t0 t1) ctx initial_cache with
    | Success ((_, g), cache) -> Inl (return_my_guard_and_tok_t g cache)
    | Error err -> Inr err
