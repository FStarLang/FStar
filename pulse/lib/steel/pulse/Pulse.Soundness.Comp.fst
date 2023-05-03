module Pulse.Soundness.Comp

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module STT = Pulse.Soundness.STT

let stc_soundness
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
                        (post1_type_bind (elab_term st.res))) =
   
  let STC _ st x dres dpre dpost = d_st in
  let res_typing = tot_typing_soundness dres in
  let pre_typing = tot_typing_soundness dpre in      
  calc (==) {
    RT.close_term (elab_term (open_term st.post x)) x;
       (==) { elab_open_commute st.post x }
    RT.close_term (RT.open_term (elab_term st.post) x) x;
       (==) { 
              elab_freevars st.post;
              RT.close_open_inverse (elab_term st.post) x
            }
    elab_term st.post;
  };
  let post_typing  = mk_t_abs_tot f g RT.pp_name_default dres dpost in
  res_typing, pre_typing, post_typing

#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 2"
let comp_typing_soundness (f:stt_env)
                          (g:env)
                          (c:comp)
                          (uc:universe)
                          (d:comp_typing f g c uc)
  : GTot (RT.tot_typing (extend_env_l f g)
                        (elab_comp c)
                        (RT.tm_type (elab_universe uc)))
         (decreases d)
  = match d with
    | CT_Tot _ t _ dt ->
      tot_typing_soundness dt
      
    | CT_ST _ st d_st -> 
      let res_typing, pre_typing, post_typing = stc_soundness d_st in
      STT.stt_typing res_typing pre_typing post_typing

    | CT_STAtomic _ i st d_i d_st -> 
      let i_typing = tot_typing_soundness d_i in
      let res_typing, pre_typing, post_typing = stc_soundness d_st in
      STT.stt_atomic_typing res_typing i_typing pre_typing post_typing

    | CT_STGhost _ i st d_i d_st -> 
      let i_typing = tot_typing_soundness d_i in
      let res_typing, pre_typing, post_typing = stc_soundness d_st in
      STT.stt_ghost_typing res_typing i_typing pre_typing post_typing
#pop-options
