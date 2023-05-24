module Pulse.Soundness.Comp

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Core
open Pulse.Soundness.Common

module R = FStar.Reflection
module RT = FStar.Reflection.Typing

val stc_soundness
  (#g:stt_env)
  (#st:st_comp)
  (d_st:st_comp_typing g st)
  
  : GTot (RT.tot_typing ( elab_env g)
                        (elab_term st.res)
                        (RT.tm_type st.u) &
          RT.tot_typing (elab_env g)
                        (elab_term st.pre)
                        vprop_tm &
          RT.tot_typing (elab_env g)
                        (mk_abs (elab_term st.res) R.Q_Explicit
                           (elab_term st.post))
                        (post1_type_bind (elab_term st.res)))

val comp_typing_soundness (g:stt_env)
                          (c:comp)
                          (uc:universe)
                          (d:comp_typing g c uc)
  : GTot (RT.tot_typing (elab_env g) (elab_comp c) (RT.tm_type uc))
