module Pulse.Soundness.While

open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Soundness.Common

module RT = FStar.Reflection.Typing

val while_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_While? d})
  (soundness: soundness_t d)
  : GTot (RT.tot_typing (extend_env_l f g)
                        (elab_st_typing d)
                        (elab_comp c))
