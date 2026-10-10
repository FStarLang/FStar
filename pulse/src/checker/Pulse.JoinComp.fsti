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
   generalized out of the leftover, which would cut the two apart; it is taken
   from the picked branch too.

   For testing that the checker rejects wrong candidates,
   `--ext pulse:join_fault=<mode>` makes this return a wrong one:
   [false] adds `pure False`; [then]/[else] return that branch's postcondition
   unchanged; [hyp] adds a fact about the branch hypothesis [hyp], which is
   provable in both branches but out of scope after the [if]; [ill_typed]
   adds an ill-typed pure fact. *)
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
