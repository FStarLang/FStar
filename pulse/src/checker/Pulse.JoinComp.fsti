(*
   Copyright 2023 Microsoft Research

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

module Pulse.JoinComp

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
module T = FStar.Tactics.V2

val infer_post' (g:env) (g':env { g' `env_extends` g })
  (u:universe) (t:typ) (x: var { lookup g' x == Some t })
  (post:term)
: T.Tac (p:post_hint_for_env g {p.g == g /\ p.effect_annot==EffectAnnotSTT})

let infer_post #g #ctxt (r:checker_result_t g ctxt NoHint)
: T.Tac (p:post_hint_for_env g {p.g == g /\ p.effect_annot==EffectAnnotSTT})
= let (| x, g', (u, t), post, k |) = r in
  infer_post' g g' u t x post

(* [p], a postcondition of the branch of [if b] selected by [then_], with each
   of its pure facts weakened to hold only under that branch's condition. *)
val guard_branch_post (#g:env) (b:term) (then_:bool) (p:post_hint_for_env g)
: T.Tac (q:post_hint_for_env g { q.effect_annot == p.effect_annot })

(* A candidate postcondition for [if b] whose branches have postconditions [p1]
   and [p2]: an slprop in which bound variable 0 is the result.

   UNTRUSTED. Nothing about the result is assumed, not even that it is
   well-scoped or well-typed. Pulse.Checker.If checks it is a well-typed slprop
   in [g] (so it cannot mention [hyp] or anything a branch bound), then proves
   it of both branches and elaborates them, before using it; a wrong candidate
   is rejected, or skipped for the next one.

   With no [pick], what the branches do not agree on is kept under the
   condition. With [Some then_], it is taken from the branch [then_] selects
   (see [guard_branch_post]) instead. With [linked], a conjunct that names a
   branch's existential witness also named by another of its conjuncts is not
   generalized out of the leftover, which would cut the two apart; [pick] then
   selects it together with the rest of that branch's leftover.

   Examples below use Pulse notation, up to renaming bound variables,
   reordering/reassociating [**], and omitting [emp]. The result variable is
   unused. Let [r:ref int], and let [P] and [Q] be opaque predicates of type
   [int -> slprop] with distinct, non-matching heads.

   * Matching resources are joined regardless of [pick] and [linked]:

       p1 = r |-> 1
       p2 = r |-> 2
       result = r |-> (if b then 1 else 2)

   * Only the unmatched part is picked, not the whole postcondition:

       p1 = r |-> 1 ** P 0
       p2 = r |-> 2 ** Q 0

     For either value of [linked]:

       pick = None:
         r |-> (if b then 1 else 2) ** (if b then P 0 else Q 0)
       pick = Some true:
         r |-> (if b then 1 else 2) ** P 0
       pick = Some false:
         r |-> (if b then 1 else 2) ** Q 0

     Picking [P 0] is useful if the prover can turn [Q 0] into [P 0],
     e.g. by folding/unfolding. If it cannot, that candidate is rejected.

   * An unmatched pure fact is guarded, not asserted of both branches:

       p1 = P 0 ** pure phi
       p2 = P 0
       result = P 0 ** pure (b == true ==> phi)

     This holds for every [pick] and [linked]. In particular, picking the
     else-branch does not discard the guarded fact from the then-branch.

   * [linked] controls whether existential witnesses may be separated:

       p1 = exists* x. r |-> x ** P x
       p2 = exists* y. r |-> y ** Q y

     With [linked = false], the matching cells are generalized over a fresh
     witness [z], independently of the witnesses still named by [P] and [Q]:

       pick = None:
         exists* z. r |-> z **
           (if b then (exists* x. P x) else (exists* y. Q y))
       pick = Some true:
         exists* z. r |-> z ** (exists* x. P x)
       pick = Some false:
         exists* z. r |-> z ** (exists* y. Q y)

     These candidates lose the connection between the cell's value and the
     predicate's argument. With [linked = true], the cell stays with its
     predicate in the leftover:

       pick = None:       if b then p1 else p2
       pick = Some true:  p1
       pick = Some false: p2

     In contrast, if [p1 = exists* x. r |-> x] and
     [p2 = exists* y. r |-> y], there is no shared witness to preserve:
     every choice of [pick] and [linked] yields [exists* z. r |-> z]. *)
val join_post_candidate (pick:option bool) (linked:bool) #g #hyp #b
    (p1:post_hint_for_env (g_with_eq g hyp b tm_true))
    (p2:post_hint_for_env (g_with_eq g hyp b tm_false))
: T.Tac term

val join_comps
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (post:post_hint_t)
: T.TacH comp_st
    (requires
      comp_post_matches_hint c_then (PostHint post) /\
      comp_post_matches_hint c_else (PostHint post) /\
      comp_pre c_then == comp_pre c_else)
    (ensures fun c ->
        st_comp_of_comp c == st_comp_of_comp c_then /\
        comp_post_matches_hint c (PostHint post))
