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

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory
module RU = Pulse.RuntimeUtils

(* For now we just create a term with the union,
but this could potentially be smarter *)
let compute_iname_join (is1 is2 : term) : term =
  tm_join_inames is1 is2
  
let lift_atomic_to_st
  (g : env)
  (e : st_term)
  (c : comp_st{C_STAtomic? c})
  (d : st_typing g e c)
  : Pure (c':comp_st & st_typing g e c')
         (requires True)
         (ensures fun (| c', _ |) ->
             st_comp_of_comp c' == st_comp_of_comp c /\
             ctag_of_comp_st c' == STT)
= let C_STAtomic _ _ c_st = c in
  let c' = C_ST c_st in
  let d' : st_typing g e c' =
    T_Lift g e c c' d (Lift_STAtomic_ST g c)
  in
  (| c', d' |)

let lift_ghost_to_atomic
  (g : env)
  (e : st_term)
  (c : comp_st{C_STGhost? c})
  (d : st_typing g e c)
  : TacS (c':comp_st & st_typing g e c')
         (requires True)
         (ensures fun (| c', _ |) ->
             st_comp_of_comp c' == st_comp_of_comp c /\
             ctag_of_comp_st c' == STT_Atomic /\
             tm_emp_inames == C_STAtomic?.inames c')
= let C_STGhost c_st = c in
  let comp_res_typing : universe_of g (comp_res c) (comp_u c) =
    let open Metatheory in
    let d = st_typing_correctness d in
    let d, _ = comp_typing_inversion d in
    let (| d, _, _, _ |) = st_comp_typing_inversion d in
    d
  in
  let w : non_informative_c g c = get_non_informative_witness g (comp_u c) (comp_res c) comp_res_typing in
  FStar.Tactics.BreakVC.break_vc(); // somehow this proof is unstable, this helps
  let c' = C_STAtomic tm_emp_inames Neutral c_st in
  let d' : st_typing g e c' =
    T_Lift g e c c' d (Lift_Ghost_Neutral g c w)
  in
  assert (st_comp_of_comp c' == st_comp_of_comp c);
  assert (ctag_of_comp_st c' == STT_Atomic);
  assert (tm_emp_inames == C_STAtomic?.inames c');
  (| c', d' |)

(* This matches the effects of the two branches, without
necessarily matching inames. *)
#push-options "--z3rlimit 20"
open Pulse.Checker.Base
(* NB: g_then and g_else are equal except for containing one extra
hypothesis according to which branch was taken. *)
let join_comps
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
  | _ -> 
    (| _, e_then_typing, e_else_typing |)
#pop-options
