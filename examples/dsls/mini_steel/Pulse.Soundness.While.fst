module Pulse.Soundness.While

module R = FStar.Reflection
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module WT = Pulse.Steel.Wrapper.Typing
module LN = Pulse.Typing.LN

#push-options "--z3rlimit_factor 4 --fuel 4 --ifuel 2"
let while_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_While? d})
  (soundness: soundness_t d)
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_While _ inv cond body inv_typing cond_typing body_typing = d in
  let rinv = mk_abs bool_tm R.Q_Explicit (elab_term inv) in
  let rinv_typing
    : RT.typing _
        (mk_exists uzero bool_tm rinv)
        vprop_tm =
    tot_typing_soundness inv_typing in
  let rinv_typing
    : RT.typing _
        rinv
        (mk_arrow (bool_tm, R.Q_Explicit) vprop_tm) =
    WT.exists_inversion rinv_typing in
  let rcond_typing
    : RT.typing _ (elab_st_typing cond_typing)
        (mk_stt_comp uzero bool_tm (mk_exists uzero bool_tm rinv) rinv) =
    soundness f g cond (comp_while_cond inv) cond_typing in

  elab_open_commute' inv tm_true 0;

  let rbody_typing
    : RT.typing _ (elab_st_typing body_typing)
        (mk_stt_comp uzero unit_tm
           (R.pack_ln (R.Tv_App rinv (true_tm, R.Q_Explicit)))
           (mk_abs unit_tm R.Q_Explicit (mk_exists uzero bool_tm rinv))) =
    
    let d = soundness f g body (comp_while_body inv) body_typing in
    let pre_eq : RT.equiv (extend_env_l f g)
                          (R.pack_ln (R.Tv_App rinv (true_tm, R.Q_Explicit)))
                          (RT.open_or_close_term' (elab_term inv) (RT.OpenWith true_tm) 0)
      = RT.EQ_Beta _ bool_tm R.Q_Explicit (elab_term inv) true_tm  in
    RT.T_Sub _ _ _ _ d
      (RT.ST_Equiv _ _ _ (RT.EQ_Sym _ _ _ (elab_stt_equiv _ _ _ _ pre_eq (RT.EQ_Refl _ _))))in


  elab_open_commute' inv tm_false 0;

  let post_eq : RT.equiv (extend_env_l f g)
                         (R.pack_ln (R.Tv_App rinv (false_tm, R.Q_Explicit)))
                         (RT.open_or_close_term' (elab_term inv) (RT.OpenWith false_tm) 0)
    = RT.EQ_Beta _ bool_tm R.Q_Explicit (elab_term inv) false_tm  in

  let post_eq = RT.EQ_Ctxt _ _ _
    (RT.Ctxt_abs_body (RT.binder_of_t_q unit_tm R.Q_Explicit) RT.Ctxt_hole) post_eq in

  let d = WT.while_typing rinv_typing rcond_typing rbody_typing in
  RT.T_Sub _ _ _ _ d (RT.ST_Equiv _ _ _ (elab_stt_equiv _ _ _ _ (RT.EQ_Refl _ _) post_eq))
#pop-options
