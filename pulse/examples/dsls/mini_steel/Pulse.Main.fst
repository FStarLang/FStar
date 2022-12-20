module Pulse.Main

module T = FStar.Tactics
module R = FStar.Reflection
module RT = Refl.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate.Pure
open Pulse.Elaborate
open Pulse.Soundness


let main' (t:term) (pre:term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.typing g (fst r) (snd r)})
  = match Pulse.Soundness.Common.check_top_level_environment g with
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

let main t pre : RT.dsl_tac_t = main' t pre

let erased_lid = ["Pulse"; "Steel"; "Wrapper"; "erased"]
let hide_lid = ["Pulse"; "Steel"; "Wrapper"; "hide"]
let reveal_lid = ["Pulse"; "Steel"; "Wrapper"; "reveal"]
let u32_lid = ["Pulse"; "Steel"; "Wrapper"; "u32"]
let ref_lid = ["Pulse"; "Steel"; "Wrapper"; "ref"]
let pts_to_lid = ["Pulse"; "Steel"; "Wrapper"; "pts_to"]
let read_lid = ["Pulse"; "Steel"; "Wrapper"; "read"]
let write_lid = ["Pulse"; "Steel"; "Wrapper"; "write"]

// "(fun (n:erased) (r:ref) (x:u32) -> \
//             { pts_to r (reveal n) } call: write(r, x))"
let bar = (
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
           (Tm_PureApp
              (Tm_PureApp
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

[@@plugin]
let check_bar (_:unit) : RT.dsl_tac_t =
  main bar Tm_Emp

// fun (n:erased) (r1:ref) (x:u32) (r2:ref) -> \\
//   {pts_to r1 (reveal n) `star` pts_to r2 (reveal n)} call: write (r1, x))

let baz = (
Tm_Abs
  (Tm_FVar erased_lid)  // n:erased
  Tm_Emp
  (
    Tm_Abs
      (Tm_FVar ref_lid)  // r1:ref
      Tm_Emp
      (
        Tm_Abs
          (Tm_FVar u32_lid)  // x:u32
          Tm_Emp
          (
            Tm_Abs
              (Tm_FVar ref_lid)  // r2:ref
              (
                Tm_Star
                  (
                    Tm_PureApp
                      (
                        Tm_PureApp
                          (Tm_FVar pts_to_lid)
                          (Tm_BVar 0)
                      )
                      (
                        Tm_PureApp
                          (Tm_FVar reveal_lid)
                          (Tm_BVar 3)
                      )
                  )
                  (
                    Tm_PureApp
                      (
                        Tm_PureApp
                          (Tm_FVar pts_to_lid)
                          (Tm_BVar 2)
                      )
                      (
                        Tm_PureApp
                          (Tm_FVar reveal_lid)
                          (Tm_BVar 3)
                      )
                  )
              )
              (
                Tm_STApp
                  (
                    Tm_PureApp
                      (
                        Tm_PureApp
                          (Tm_FVar write_lid)
                          (Tm_BVar 3)
                      )
                      (Tm_BVar 2)
                  )
                  (Tm_BVar 1)
              )
          )
      )
  )
)

[@@plugin]
let check_baz (_:unit) : RT.dsl_tac_t =
  main baz Tm_Emp
