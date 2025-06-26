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
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover


let st_ghost_as_atomic_matches_post_hint
  (c:comp { C_STGhost? c })
  (post:post_hint_t { EffectAnnotAtomicOrGhost? post.effect_annot })
  : Lemma (requires comp_post_matches_hint c (Some post))
          (ensures comp_post_matches_hint (st_ghost_as_atomic c) (Some post)) = ()

(* This matches the effects of the two branches, without
necessarily matching inames. *)
#push-options "--z3rlimit_factor 4"
open Pulse.Checker.Base
(* NB: g_then and g_else are equal except for containing one extra
hypothesis according to which branch was taken. *)
let rec join_comps
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  (post:post_hint_t)
  : TacS (c:comp_st &
          st_typing g_then e_then c &
          st_typing g_else e_else c)
         (requires
            comp_post_matches_hint c_then (Some post) /\
            comp_post_matches_hint c_else (Some post) /\
            comp_pre c_then == comp_pre c_else)
         (ensures fun (| c, _, _ |) ->
           st_comp_of_comp c == st_comp_of_comp c_then /\
           comp_post_matches_hint c (Some post))
= let g = g_then in
  assert (st_comp_of_comp c_then == st_comp_of_comp c_else);
  match c_then, c_else with
  | C_STAtomic _ obs1 _, C_STAtomic _ obs2 _ ->
    let obs = join_obs obs1 obs2 in
    let e_then_typing = T_Lift _ _ _ _ e_then_typing (Lift_Observability g_then c_then obs) in
    let e_else_typing = T_Lift _ _ _ _ e_else_typing (Lift_Observability g_else c_else obs) in
    (| _, e_then_typing, e_else_typing |)
  | C_STGhost _ _, C_STGhost _ _
  | C_ST _, C_ST _ -> (| _, e_then_typing, e_else_typing |)

  | _ ->
    assert (EffectAnnotAtomicOrGhost? post.effect_annot);
    match c_then, c_else with
    | C_STGhost _ _, C_STAtomic _ _ _ ->
      let d : st_typing g_then e_then (st_ghost_as_atomic c_then) =
        lift_ghost_atomic e_then_typing in
      st_ghost_as_atomic_matches_post_hint c_then post;
      join_comps _ _ _ d _ _ _ e_else_typing post

    | C_STAtomic _ _ _, C_STGhost _ _ ->
      let d = lift_ghost_atomic e_else_typing in
      st_ghost_as_atomic_matches_post_hint c_else post;
      join_comps _ _ _ e_then_typing _ _ _ d post
#pop-options
