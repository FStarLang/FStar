module Pulse.Soundness.Match

open Pulse.Soundness.Common
open Pulse.Syntax.Base
open Pulse.Typing
open Pulse.Elaborate.Core
open Pulse.Elaborate.Pure
module RT = FStar.Reflection.Typing

val match_soundness
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c{T_Match? d})
  (soundness:soundness_t d)
  (ct_soundness: (g:stt_env -> c:comp -> uc:universe ->
                  d':comp_typing g c uc{d' << d} ->
              GTot (RT.tot_typing (elab_env g)
                              (elab_comp c)
                              (RT.tm_type uc))))
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c))
