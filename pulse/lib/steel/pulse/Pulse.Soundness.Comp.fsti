module Pulse.Soundness.Comp

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Soundness.Common

module R = FStar.Reflection
module RT = FStar.Reflection.Typing

val stc_soundness
  (#f:stt_env)
  (#g:env)
  (#st:st_comp)
  (d_st:st_comp_typing f g st)
  
  : GTot (RT.tot_typing (extend_env_l f g)
                        (elab_term st.res)
                        (RT.tm_type (elab_universe st.u)) &
          RT.tot_typing (extend_env_l f g)
                        (elab_term st.pre)
                        vprop_tm &
          RT.tot_typing (extend_env_l f g)
                        (mk_abs (elab_term st.res) R.Q_Explicit
                           (elab_term st.post))
                        (post1_type_bind (elab_term st.res)))

val comp_typing_soundness (f:stt_env)
                          (g:env)
                          (c:comp)
                          (uc:universe)
                          (d:comp_typing f g c uc)
  : GTot (RT.tot_typing (extend_env_l f g) (elab_comp c) (RT.tm_type (elab_universe uc)))
