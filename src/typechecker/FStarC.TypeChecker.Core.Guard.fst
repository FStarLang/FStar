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
module FStarC.TypeChecker.Core.Guard

(* See the interface. *)

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
open FStarC.TypeChecker.Core.Util
open FStarC.TypeChecker.Core.Facts
open FStarC.TypeChecker.Core.Cache

let mk_forall_l_gen (keep_unit:bool) (us:universes) (xs:binders) (t:term)
  : ML term
  = (* As [Env.close_guard], a quantifier over a null binder of (unrefined)
       [unit], e.g. of a thunk [fun () -> ...], is dropped (unless
       [keep_unit], for the binders of the definition itself, e.g. of
       [let f () = ...], which TcTerm has in its environment when it
       discharges the guard), so that goals handed to tactics, and the
       context of a failed goal, are as with TcTerm. Named binders are kept, e.g. those
       of the thunks of a [calc]: the SMT encoding assumes a quantifier-free
       conjunct of a guard when proving the next ones
       ([ErrorReporting.split_goals]), and keeping the quantifier keeps a
       proof step out of the context of the next. (Other null binders, e.g.
       [_:squash p], are hypotheses and are kept too.) *)
    let vacuous (x:binder) (t:term) : ML bool =
      not keep_unit &&
      S.is_null_binder x &&
      (match (Subst.compress x.binder_bv.sort).n with
       | Tm_fvar fv -> S.fv_eq_lid fv PC.unit_lid
       | _ -> false) &&
      not (mem x.binder_bv (FStarC.Syntax.Free.names t))
    in
    FStarC.List.fold_right2
        (fun u x t -> if vacuous x t then t else U.mk_forall u x.binder_bv t)
        us
        xs
        t

let mk_forall_l us xs t : ML term = mk_forall_l_gen false us xs t

let close_with_definition (x:binder) (u:universe) (t:term) (g:typ)
: ML typ
= (* Oriented as TcTerm's [e == x] (see [TcUtil.mk_binder_eqn]), which
     is how the hypothesis is shown in the context of a failed goal. *)
  let g' = U.mk_imp (U.mk_eq2 u x.binder_bv.sort t (S.bv_to_name x.binder_bv)) g in
  U.mk_forall u x.binder_bv g'

let weaken_subtyping (p:term) (g:term)
: ML term
= U.mk_imp p g

let guard (g:env) (guard:typ)
  : result unit
  = fun ctx cache ->
    let guard = cache_key guard in
    (match! raw_lookup_guard guard with
     | Some ge ->
       if ge.ge_gamma `context_included` g.tcenv.gamma
       then return () //cache hit 
       else (
         insert_guard g guard ;!
         return_with_guard () (Some guard)
       )
     | _ ->
       insert_guard g guard ;!
       return_with_guard () (Some guard)) ctx cache

(* Emit [guard], a transformation (closure, weakening) of a guard that a
   sub-computation emitted and whose guard the caller has consumed. It must
   not be dropped as a cache hit: when the transformation is trivial (e.g.,
   closing over no binders), the entry found is the one just inserted by the
   sub-computation, whose guard is not otherwise part of the result. *)
let reemit_guard (g:env) (guard:typ)
  : result unit
  = fun ctx cache ->
    let guard = cache_key guard in
    (insert_guard g guard ;!
     return_with_guard () (Some guard)) ctx cache

(* The guard [phi] about the witness of a refinement subtyping, whose
   subterms have the facts [fs]. The type synthesized for an application is
   its head's result type, which says nothing about its arguments; so also
   assume what the types of its arguments say about them. TcTerm makes those
   facts available by binding every argument to a name of its type. *)
let witness_guard (g:env) (fs:Thunk.t (list term)) (phi:typ)
  : ML (result unit)
  = let facts = dedup_facts (Thunk.force fs) in
    if !dbg_facts then Format.print2 "witness_guard %s: %s facts\n" (show phi) (show (List.length facts));
    match facts with
    | [] -> guard g phi
    | _ -> guard g (U.mk_imp (U.mk_conj_l facts) phi)

(* Either of two checks suffices: if both have guards, their disjunction is
   the guard. The caches of both are then dropped, since their entries would
   claim that their own guards, rather than the disjunction, were emitted.
   But a quantifier-free guard of [f1] is taken on its own: a disjunction is
   a burden on the SMT solver, which case-splits on it wherever it is a
   hypothesis, i.e. in every later goal of a split query. *)
let either_guard (f1 f2: unit -> ML (result unit)) : result unit
  = fun ctx cache ->
      match f1 () ctx cache with
      | Success (((), None), cache1) -> Success (((), None), cache1)
      | Success (((), Some p1), cache1) when quantifier_free p1 ->
        Success (((), Some p1), cache1)
      | r1 ->
        match f2 () ctx cache with
        | Success (((), None), cache2) -> Success (((), None), cache2)
        | r2 ->
          match r1, r2 with
          | Success (((), Some p1), _), Success (((), Some p2), _) ->
            Success (((), Some (U.mk_disj p1 p2)), cache)
          | Success (((), Some p1), cache1), Error _ -> Success (((), Some p1), cache1)
          | Error _, Success (((), Some p2), cache2) -> Success (((), Some p2), cache2)
          | Error e, _ -> Error e

let with_binders (#a:Type) (initial_env:env) (xs:binders) (us:universes) (f:result a)
  : result a
  = with_guard f
    (function
      | Inr err -> fail_propagate err
      | Inl (res, None) -> return res
      | Inl (res, Some form) ->
        let form = mk_forall_l_gen initial_env.at_top us xs form in
        reemit_guard initial_env form ;!
        return res)

(* As [with_binders] for one binder; if its sort is a refinement
   [y:t{phi}], quantifies over [t] and assumes [phi], as TcTerm's guards
   for the domains of arrows do (see [Rel]): the refinement is then shown
   as a hypothesis in the context of a failed goal. *)
let with_binder_unrefined (#a:Type) (initial_env:env) (x:binder) (u:universe) (f:result a)
  : ML (result a)
  = match (Subst.compress (U.flatten_refinement x.binder_bv.sort)).n with
    | Tm_refine {b=y; phi} ->
      with_guard f
      (function
        | Inr err -> fail_propagate err
        | Inl (res, None) -> return res
        | Inl (res, Some form) ->
          let phi = Subst.subst [DB(0, x.binder_bv)] phi in
          let xb = { x with binder_bv = { x.binder_bv with sort = y.sort } } in
          let form = mk_forall_l [u] [xb] (U.mk_imp phi form) in
          reemit_guard initial_env form ;!
          return res)
    | _ -> with_binders initial_env [x] [u] f

let weaken #a (initial_env:env) (p:term) (f:result a)
: result a
= with_guard f
  (function
    | Inr err -> fail_propagate err
    | Inl (res, None) -> return res
    | Inl (res, Some form) ->
      let form = weaken_subtyping p form in
      reemit_guard initial_env form ;!
      return res)

(* Weaken the guard of [f] with a branch hypothesis (see
   [branch_conditions]), unless it is trivial. *)
let weaken_branch #a (initial_env:env) (hyp:typ) (f:result a)
: ML (result a)
= if U.is_t_true hyp then f else
  with_guard f
  (function
    | Inr err -> fail_propagate err
    | Inl (res, None) -> return res
    | Inl (res, Some form) ->
      reemit_guard initial_env (U.mk_imp hyp form) ;!
      return res)

let weaken_with_guard_formula env (p:CommonBase.guard_formula) (g:result 'a)
  = match p with
    | CommonBase.Trivial -> g
    | CommonBase.NonTrivial p -> weaken env p g

(* Label the guard of [f] with [msg], at [r], for the SMT solver to report
   when it cannot prove it (see [ErrorReporting.split_goals], where the
   innermost label wins). The message is only computed if there is a guard. *)
let label_guard (#a:Type) (g:env) (r:R.t) (msg:unit -> ML Errors.error_message) (f:result a)
  : result a
  = with_guard f
    (function
      | Inr err -> fail_propagate err
      | Inl (res, None) -> return res
      | Inl (res, Some form) ->
        reemit_guard g (VCUtil.label (msg ()) r form) ;!
        return res)

(* Locate the goals of the guard of [f] at [r], unless they have a more
   precise position (within [r]): the message "Could not prove
   post-condition" is only a position for [ErrorReporting], which reports an
   inner label, if any, or the message of an outer one, instead. E.g. the
   guard of checking a function body against its annotated computation type
   is located at the body, as by TcTerm (see [TcTerm.check_expected_effect]). *)
let label_position (#a:Type) (g:env) (r:R.t) (f:result a)
  : result a
  = label_guard g r (fun () -> Errors.mkmsg "Could not prove post-condition") f

let label_postcondition (#a:Type) (g:env) (at:term) (f:result a)
  : result a
  = label_position g at.pos f

(* As TcTerm (see [TcTerm.value_check_expected_typ]), the guard of a subtyping
   [t0 <: t1] of a term [e] is labeled "Subtyping check failed" at [e], except
   for a value of type [unit] at [squash p], e.g. a [()] given for a
   precondition: reporting that as "expected squash p, got unit" would bury
   the obligation [p], which is only located at [e]. *)
let label_subtyping (#a:Type) (g:env) (e:term) (t0 t1:typ) (f:result a)
  : ML (result a)
  = let is_value =
      match (Subst.compress (U.unmeta e)).n with
      | Tm_constant _ | Tm_name _ -> true
      | _ -> false
    in
    if is_value && U.is_unit t0 && Some? (U.un_squash t1)
    then (* The obligation is still reported at [e], as by TcTerm. *)
      label_position g e.pos f
    else label_guard g e.pos (fun () -> Err.subtyping_failed g.tcenv t0 t1 ()) f

(* [e <: t by tac]: as in [TcTerm], the guard of checking [e] against [t] is
   left to [tac], even when trivial (so that [e <: t by fail ""] fails). *)
let with_ascription_tactic (#a:Type) (g:env) (tac:option term) (f:unit -> ML (result a))
  : ML (result a)
  = match tac with
    | None -> f ()
    | Some tac ->
      with_guard (f ()) (function
        | Inr err -> fail_propagate err
        | Inl (res, phi) ->
          let phi = match phi with | None -> U.t_true | Some phi -> phi in
          reemit_guard g (CommonBase.mk_by_tactic tac (U.mk_squash phi)) ;!
          return res)

(* The conditions of a branch, as TcTerm has them (see
   [TcUtil.get_neg_branch_conds]). The path condition of a branch, a
   proposition, is the conjunction of the negations of the conditions of the
   branches before it; [False] after an irrefutable pattern. Given it, the
   branch condition [bc] of a branch (if its pattern is refutable) and the
   equation [eq] of the scrutinee with its pattern, returns:
   - the hypothesis under which the branch is taken, which does not mention
     the pattern variables: the path condition and [bc], as one hypothesis;
   - that, and [eq];
   - the path condition of the next branch.
   Of a branch, the guard is [hyp ==> forall xs. eq ==> G], where [xs] are
   the pattern variables: the equation is the last hypothesis (tactics look
   it up). *)
let branch_conditions (path_condition:typ) (branch_condition:option term) (eq:typ)
  : ML (typ & typ & typ)
  = let hyp =
      match branch_condition with
      | None -> path_condition
      | Some bc -> U.mk_conj_simp path_condition (U.b2t bc)
    in
    let next =
      match branch_condition with
      | None -> U.t_false
      | Some bc -> U.mk_conj_simp path_condition (U.mk_neg (U.b2t bc))
    in
    hyp, U.mk_conj_simp hyp eq, next

(* The obligation that no branch is missing, given the path condition after
   the last branch, labeled as by TcTerm. *)
let exhaustiveness_obligation (r:R.t) (path_condition:typ) : ML (option typ) =
  if U.is_t_false path_condition then None
  else Some (VCUtil.label Err.exhaustiveness_check r (U.mk_imp path_condition U.t_false))
