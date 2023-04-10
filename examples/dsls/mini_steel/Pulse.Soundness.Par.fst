module Pulse.Soundness.Par

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module R = FStar.Reflection

module PReflUtil = Pulse.Reflection.Util
module WT = Pulse.Steel.Wrapper.Typing


#push-options "--z3rlimit_factor 4 --fuel 4 --ifuel 1"
let par_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_Par? d})
  (soundness: soundness_t d)
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_Par _ eL cL eR cR x cL_typing cR_typing eL_typing eR_typing = d in

  let ru = elab_universe (comp_u cL) in
  let raL = elab_term (comp_res cL) in
  let raR = elab_term (comp_res cR) in
  let rpreL = elab_term (comp_pre cL) in
  let rpostL = mk_abs raL R.Q_Explicit (elab_term (comp_post cL)) in
  let rpreR = elab_term (comp_pre cR) in
  let rpostR = mk_abs raR R.Q_Explicit (elab_term (comp_post cR)) in
  let reL = elab_st_typing eL_typing in
  let reR = elab_st_typing eR_typing in

  let reL_typing
    : RT.typing _ reL (elab_comp cL) =
    soundness f g eL cL eL_typing in

  let reR_typing
    : RT.typing _ reR (elab_comp cR) =
    soundness f g eR cR eR_typing in

  let (raL_typing, rpreL_typing, rpostL_typing)
    : (RT.typing _ raL (R.pack_ln (R.Tv_Type ru)) &
       RT.typing _ rpreL vprop_tm &
       RT.typing _ rpostL (mk_arrow (raL, R.Q_Explicit) vprop_tm)) =

    inversion_of_stt_typing f g cL ru (Comp.comp_typing_soundness f g cL (comp_u cL) cL_typing) in

  let (raR_typing, rpreR_typing, rpostR_typing)
    : (RT.typing _ raR (R.pack_ln (R.Tv_Type ru)) &
       RT.typing _ rpreR vprop_tm &
       RT.typing _ rpostR (mk_arrow (raR, R.Q_Explicit) vprop_tm)) =

    inversion_of_stt_typing f g cR ru (Comp.comp_typing_soundness f g cR (comp_u cR) cR_typing) in

  let uL = comp_u cL in
  let uR = comp_u cR in
  let aL = comp_res cL in
  let aR = comp_res cR in
  let postL = comp_post cL in
  let postR = comp_post cR in
  let x_tm = term_of_var x in
  let rx_tm = RT.var_as_term x in

  elab_open_commute' postL (mk_fst uL uR aL aR x_tm) 0;
  elab_open_commute' postR (mk_snd uL uR aL aR x_tm) 0;

  let post_body_eq : RT.equiv (extend_env_l f g)
    (mk_star (R.pack_ln (R.Tv_App rpostL (PReflUtil.mk_fst ru ru raL raR rx_tm, R.Q_Explicit)))
             (R.pack_ln (R.Tv_App rpostR (PReflUtil.mk_snd ru ru raL raR rx_tm, R.Q_Explicit))))
    (elab_term (Tm_Star (open_term' postL (mk_fst uL uR aL aR x_tm) 0)
                        (open_term' postR (mk_snd uL uR aL aR x_tm) 0)))
    = mk_star_equiv _ _ _ _ _
        (RT.EQ_Beta _ raL _ (elab_term postL) _)
        (RT.EQ_Beta _ raR _ (elab_term postR) _) in

  let post_eq
    : RT.equiv (extend_env_l f g)
               (mk_abs _ R.Q_Explicit _)
               (mk_abs _ R.Q_Explicit _)
    = RT.equiv_abs _ _ x post_body_eq in

  let d = WT.par_typing x raL_typing raR_typing rpreL_typing rpostL_typing
    rpreR_typing rpostR_typing
    reL_typing reR_typing in
  
  RT.T_Sub _ _ _ _ d
    (RT.ST_Equiv _ _ _ (elab_stt_equiv _ c _ _ (RT.EQ_Refl _ _) post_eq))
#pop-options
