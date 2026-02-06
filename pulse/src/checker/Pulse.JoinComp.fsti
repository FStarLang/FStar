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
  #u #t (x: var { lookup g' x == Some t }) (t_typ: universe_of g' t u)
  #post (post_typing: tot_typing g' post tm_slprop)
: T.Tac (p:post_hint_for_env g {p.g == g /\ p.effect_annot==EffectAnnotSTT})

let infer_post #g #ctxt (r:checker_result_t g ctxt NoHint)
: T.Tac (p:post_hint_for_env g {p.g == g /\ p.effect_annot==EffectAnnotSTT})
= let (| x, g', (| u, t, t_typ |), (| post, post_typing |), k |) = r in
  infer_post' g g' x t_typ post_typing

val join_post #g #hyp #b
    (p1:post_hint_for_env (g_with_eq g hyp b tm_true))
    (p2:post_hint_for_env (g_with_eq g hyp b tm_false))
: T.Tac (post_hint_for_env g)

val join_comps
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  (post:post_hint_t)
: T.TacH (c:comp_st &
        st_typing g_then e_then c &
        st_typing g_else e_else c)
    (requires
      comp_post_matches_hint c_then (PostHint post) /\
      comp_post_matches_hint c_else (PostHint post) /\
      comp_pre c_then == comp_pre c_else)
    (ensures fun (| c, _, _ |) ->
        st_comp_of_comp c == st_comp_of_comp c_then /\
        comp_post_matches_hint c (PostHint post))
