module Pulse.Soundness.Exists

open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Soundness.Common

module RT = FStar.Reflection.Typing

val intro_exists_erased_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_IntroExistsErased? d})
  : GTot (RT.tot_typing (extend_env_l f g)
                        (elab_st_typing d)
                        (elab_comp c))

val intro_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_IntroExists? d })
  : GTot (RT.tot_typing (extend_env_l f g)
                        (elab_st_typing d)
                        (elab_comp c))

val elim_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_ElimExists? d})
  : GTot (RT.tot_typing (extend_env_l f g)
                        (elab_st_typing d)
                        (elab_comp c))


