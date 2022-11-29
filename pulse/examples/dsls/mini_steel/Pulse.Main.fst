module Pulse.Main

module T = FStar.Tactics
module RT = Refl.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate.Pure
open Pulse.Elaborate
open Pulse.Soundness

let main (t:term) (pre:pure_term) : RT.dsl_tac_t =
  fun g ->
  let (| ty, pre_typing |) = check_tot g [] pre in
  if ty = Tm_VProp
  then let pre_typing : tot_typing g [] pre Tm_VProp = E pre_typing in
       let (| c, t_typing |) = check g [] t pre pre_typing in
       let refl_e = elab_src_typing t_typing in
       let refl_t = elab_pure_comp c in
       soundness_lemma g [] t c t_typing;
       (refl_e, refl_t)
  else T.fail "pulse main: cannot typecheck pre at type vprop"


(***** tests *****)

open Steel.Effect.Common
open Steel.ST.Util

// #set-options "--debug Pulse.Main --debug_level ReflTc,Extreme,Rel --ugly"
%splice_t[foo] (main (Tm_Constant (Bool true)) Tm_Emp)
