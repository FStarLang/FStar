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

val elab_frame_typing (f:stt_env)
                      (g:env)
                      (e:R.term)
                      (c:ln_comp)
                      (frame:pure_term)
                      (frame_typing: tot_typing f g frame Tm_VProp)
                      (e_typing: RT.typing (extend_env_l f g) e (elab_pure_comp c))
  : GTot (RT.typing (extend_env_l f g) (elab_frame c frame e) (elab_pure_comp (add_frame c frame)))
