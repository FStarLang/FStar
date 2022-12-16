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
  match check_top_level_environment g with
  | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
  | Some g ->
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

open Pulse.Steel.Wrapper

%splice_t[foo] (main (Tm_Constant (Bool true)) Tm_Emp)

let erased_lid = ["Pulse"; "Steel"; "Wrapper"; "erased"]
let hide_lid = ["Pulse"; "Steel"; "Wrapper"; "hide"]
let reveal_lid = ["Pulse"; "Steel"; "Wrapper"; "reveal"]
let u32_lid = ["Pulse"; "Steel"; "Wrapper"; "u32"]
let ref_lid = ["Pulse"; "Steel"; "Wrapper"; "ref"]
let pts_to_lid = ["Pulse"; "Steel"; "Wrapper"; "pts_to"]
let read_lid = ["Pulse"; "Steel"; "Wrapper"; "read"]
let write_lid = ["Pulse"; "Steel"; "Wrapper"; "write"]

[@@ expect_failure]
%splice_t[bar] (main

(
Tm_Abs
  (Tm_FVar erased_lid)  //n:erased u32
  Tm_Emp
  (Tm_Abs
     (Tm_FVar ref_lid)  //r:ref
     Tm_Emp
     (Tm_Abs
        (Tm_FVar u32_lid)  //x:u32
        (Tm_PureApp
          (Tm_PureApp
             (Tm_FVar pts_to_lid)
             (Tm_BVar 1))
          (Tm_PureApp
             (Tm_FVar reveal_lid)
             (Tm_BVar 2))
        )
        (Tm_STApp
           (Tm_STApp
              (Tm_STApp
                 (Tm_FVar write_lid)
                 (Tm_BVar 2)
              )
              (Tm_BVar 1)
           )
           (Tm_BVar 0)
        )
     )
  )
)
Tm_Emp
)
