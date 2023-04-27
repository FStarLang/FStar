module Pulse.Soundness.WithLocal

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

#push-options "--z3rlimit_factor 10"

let withlocal_soundness #f #g #t #c d soundness =
  let T_WithLocal _ init body init_t c x init_typing init_t_typing c_typing body_typing = d in
  let CT_ST _ st st_typing = c_typing in
  
  let rg = extend_env_l f g in
  let ru = elab_universe (comp_u c) in
  let ra = elab_term init_t in
  let rinit = elab_term init in
  let rpre = elab_term (comp_pre c) in
  let rret_t = elab_term (comp_res c) in
  let rpost = mk_abs rret_t R.Q_Explicit (elab_term (comp_post c)) in
  let rbody =
    RT.mk_abs (PReflUtil.mk_ref ra) R.Q_Explicit
      (RT.open_or_close_term' (elab_st_typing body_typing) (RT.CloseVar x) 0) in
  
  let a_typing:RT.typing rg ra (R.pack_ln (R.Tv_Type (R.pack_universe R.Uv_Zero))) =
    tot_typing_soundness init_t_typing in
  
  let init_typing:RT.typing rg rinit ra =
    tot_typing_soundness init_typing in

  let cres_typing, cpre_typing, cpost_typing =
    Pulse.Soundness.Comp.stc_soundness st_typing in

  let pre_typing:RT.typing rg rpre vprop_tm = cpre_typing in
  let ret_t_typing:RT.typing rg rret_t (R.pack_ln (R.Tv_Type ru)) = cres_typing in
  let post_typing:RT.typing rg rpost (mk_arrow (rret_t, R.Q_Explicit) vprop_tm) =
    cpost_typing in

  let elab_body_comp = elab_comp (comp_withlocal_body x init_t init c) in

  let rbody_typing
    : RT.typing (extend_env_l f ((x, Inl (mk_ref init_t))::g))
                (elab_st_typing body_typing)
                elab_body_comp =
    soundness _ _ _ _ body_typing in

  let ref_init_t_typing : typing f g (mk_ref init_t) (Tm_Type U_zero) =
    magic () in

  let rref_init_t_typing
    : RT.typing (extend_env_l f g)
                (elab_term (mk_ref init_t))
                (elab_comp (C_Tot (Tm_Type U_zero))) = magic () in

  assume (RT.open_or_close_term' (elab_st_typing body_typing) (RT.CloseVar x) 0 ==
          RT.close_term (elab_st_typing body_typing) x);

  let rbody_typing
    : RT.typing (extend_env_l f g)
                rbody
                (mk_arrow (PReflUtil.mk_ref ra, R.Q_Explicit)
                          (elab_comp (close_comp (comp_withlocal_body x init_t init c) x))) =
    mk_t_abs _ _ #_ #_ #_ #ref_init_t_typing RT.pp_name_default rref_init_t_typing rbody_typing in

  let rbody_typing
    : RT.typing
        (extend_env_l f g)
        rbody
        (mk_arrow
           (PReflUtil.mk_ref ra, R.Q_Explicit)
           (mk_stt_comp ru rret_t
              (mk_star rpre (PReflUtil.mk_pts_to ra (RT.bound_var 0) full_perm_tm rinit))
              (WT.with_local_bodypost rpost ra rret_t x))) = magic () in

  WT.with_local_typing x a_typing init_typing pre_typing ret_t_typing post_typing rbody_typing
