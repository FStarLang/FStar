module Pulse.Soundness.Frame
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

let elab_frame (c:pure_comp { C_ST? c }) (frame:pure_term) (e:R.term) =
  let C_ST s = c in
  Pulse.Elaborate.mk_frame s.u (elab_pure s.res) (elab_pure s.pre) (elab_comp_post c) (elab_pure frame) e

val elab_frame_typing (f:stt_env)
                      (g:env)
                      (e:R.term)
                      (c:ln_comp)
                      (frame:pure_term)
                      (frame_typing: tot_typing f g frame Tm_VProp)
                      (e_typing: RT.typing (extend_env_l f g) e (elab_pure_comp c))
  : GTot (RT.typing (extend_env_l f g) (elab_frame c frame e) (elab_pure_comp (add_frame c frame)))
