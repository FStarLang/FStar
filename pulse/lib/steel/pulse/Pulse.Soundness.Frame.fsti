module Pulse.Soundness.Frame
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

val elab_frame_typing (g:stt_env)
                      (e:R.term)
                      (c:ln_comp)
                      (frame:term)
                      (frame_typing: tot_typing g frame tm_vprop)
                      (e_typing: RT.tot_typing (elab_env g) e (elab_comp c))
  : GTot (RT.tot_typing (elab_env g)
                        (elab_frame c frame e)
                        (elab_comp (add_frame c frame)))
