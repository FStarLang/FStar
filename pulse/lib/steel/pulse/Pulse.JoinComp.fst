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
  let w : non_informative_c g c = get_non_informative_witness g (comp_u c) (comp_res c) in
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
let join_comp_effects
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : TacS (c_then':comp_st &
          c_else':comp_st &
          st_typing g_then e_then c_then' &
          st_typing g_else e_else c_else')
         (requires True) // comp_pre c_then == comp_pre c_else)
         (ensures fun (| c_then', c_else', _, _ |) ->
            st_comp_of_comp c_then' == st_comp_of_comp c_then /\
            st_comp_of_comp c_else' == st_comp_of_comp c_else /\
            ctag_of_comp_st c_then' == ctag_of_comp_st c_else')
= let g = g_then in
  match c_then, c_else with
  | C_STGhost _, C_STGhost _ 
  | C_STAtomic _ _ _, C_STAtomic _ _ _
  | C_ST _, C_ST _ ->
    (* Nothing to do *)
    (| c_then, c_else, e_then_typing, e_else_typing |)

  | C_STAtomic _ _ _ , C_ST _ ->
    let (| c_then', e_then_typing' |) = lift_atomic_to_st g_then e_then c_then e_then_typing in
    (| c_then', c_else, e_then_typing', e_else_typing |)

  | C_ST _, C_STAtomic _ _ _ ->
    let (| c_else', e_else_typing' |) = lift_atomic_to_st g_else e_else c_else e_else_typing in
    (| c_then, c_else', e_then_typing, e_else_typing' |)

  | C_STGhost _, C_STAtomic _ _ _ ->
    let (| c_then', e_then_typing' |) = lift_ghost_to_atomic g_then e_then c_then e_then_typing in
    (| c_then', c_else, e_then_typing', e_else_typing |)

  | C_STAtomic _ _ _, C_STGhost _ ->
    let (| c_else', e_else_typing' |) = lift_ghost_to_atomic g_else e_else c_else e_else_typing in
    (| c_then, c_else', e_then_typing, e_else_typing' |)

  | C_STGhost _, C_ST _ ->
    let (| c_then', e_then_typing' |) = lift_ghost_to_atomic g_then e_then c_then  e_then_typing  in
    let (| c_then', e_then_typing' |) = lift_atomic_to_st    g_then e_then c_then' e_then_typing' in
    (| c_then', c_else, e_then_typing', e_else_typing |)

  | C_ST _, C_STGhost _ ->
    let (| c_else', e_else_typing' |) = lift_ghost_to_atomic g_else e_else c_else  e_else_typing  in
    let (| c_else', e_else_typing' |) = lift_atomic_to_st    g_else e_else c_else' e_else_typing' in
    (| c_then, c_else', e_then_typing, e_else_typing' |)
#pop-options

(* Takes the two branches, with already matched effect,
and matches their invariants (unless C_ST) *)
#push-options "--z3rlimit 20"
let join_comp_inames
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : TacS (c_then':comp_st &
          c_else':comp_st &
          st_typing g_then e_then c_then' &
          st_typing g_else e_else c_else')
         (requires ctag_of_comp_st c_then == ctag_of_comp_st c_else)
         (ensures fun (| c_then', c_else', _, _ |) ->
            st_comp_of_comp c_then' == st_comp_of_comp c_then /\
            st_comp_of_comp c_else' == st_comp_of_comp c_else /\
            ctag_of_comp_st c_then' == ctag_of_comp_st c_then /\
            ctag_of_comp_st c_else' == ctag_of_comp_st c_else /\
            inames_of_comp c_then' == inames_of_comp c_else' /\
            obs_of_comp c_then' == obs_of_comp c_else'
         )
= match c_then, c_else with
  | C_ST _, C_ST _
  | C_STGhost _, C_STGhost _ ->
    (| c_then, c_else, e_then_typing, e_else_typing |)

  | C_STAtomic inames1 obs1 stc_then, C_STAtomic inames2 obs2 stc_else ->
    if eq_tm inames1 inames2 && obs1 = obs2 then
      (* easy case; an optimization *)
      (| c_then, c_else, e_then_typing, e_else_typing |)
    else (
      let is = compute_iname_join inames1 inames2 in
      // FIXME: this should come from some meta-theorem, we always have is1 `subset` join is1 is2
      let tok1 : prop_validity g_then (tm_inames_subset inames1 is) = RU.magic () in
      let tok2 : prop_validity g_else (tm_inames_subset inames2 is) = RU.magic () in
      let e_then_typing = T_Sub _ _ _ _ e_then_typing (STS_AtomicInvs g_then stc_then inames1 is obs1 (join_obs obs1 obs2) tok1) in
      let e_else_typing = T_Sub _ _ _ _ e_else_typing (STS_AtomicInvs g_else stc_else inames2 is obs2 (join_obs obs1 obs2) tok2) in
      (| C_STAtomic is _ stc_then, C_STAtomic is _ stc_else, e_then_typing, e_else_typing |)
    )

#pop-options

#push-options "--z3rlimit 20"
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
  : TacS (c:comp_st &
          st_typing g_then e_then c &
          st_typing g_else e_else c)
         (requires comp_pre c_then == comp_pre c_else)
         (ensures fun (| c, _, _ |) -> st_comp_of_comp c == st_comp_of_comp c_then)
=
  let g = g_then in
  if not (eq_st_comp (st_comp_of_comp c_then) (st_comp_of_comp c_else)) then
    fail g None "Cannot combine then and else branches (different st_comp)";

  let (| c_then', c_else', e_then_typing', e_else_typing' |) =
    join_comp_effects g_then e_then c_then e_then_typing g_else e_else c_else e_else_typing in
  assert (ctag_of_comp_st c_then' == ctag_of_comp_st c_else');
  let (| c_then'', c_else'', e_then_typing'', e_else_typing'' |) =
    join_comp_inames g_then e_then c_then' e_then_typing' g_else e_else c_else' e_else_typing' in
  assert (c_then'' == c_else'');
  (| c_then'', e_then_typing'', e_else_typing'' |)
#pop-options
