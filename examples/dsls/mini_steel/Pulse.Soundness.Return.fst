module Pulse.Soundness.Return

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
module LN = Pulse.Typing.LN

#push-options "--z3rlimit_factor 4 --fuel 8 --ifuel 2"
let return_soundess
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_Return? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_Return _ ctag use_eq u t e post x t_typing e_typing post_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let re = elab_term e in
  let rpost = elab_term post in
  let rpost_abs = mk_abs rt R.Q_Explicit rpost in
  let rt_typing : RT.typing _ rt (R.pack_ln (R.Tv_Type ru)) =
    tot_typing_soundness t_typing in
  let re_typing : RT.typing _ re rt =
    tot_typing_soundness e_typing in
  let rpost_abs_typing
    : RT.typing _ rpost_abs
                  (mk_arrow (rt, R.Q_Explicit) vprop_tm) =
    mk_t_abs_tot f g RT.pp_name_default t_typing post_typing in
  
  let rx_tm = RT.var_as_term x in
  let elab_c_pre = RT.open_or_close_term' rpost (RT.OpenWith re) 0 in
  let pre_eq
    : RT.equiv (extend_env_l f g)
               (R.pack_ln (R.Tv_App rpost_abs (re, R.Q_Explicit)))
               elab_c_pre
    = RT.EQ_Beta (extend_env_l f g) rt R.Q_Explicit rpost re in  
  
  let comp_equiv_noeq (_:unit{use_eq == false})
    : (match ctag with
       | STT -> RT.equiv (extend_env_l f g)
                         (WT.return_stt_noeq_comp ru rt re rpost_abs)
                         (elab_comp c)
       | STT_Atomic ->
         RT.equiv (extend_env_l f g)
                  (WT.return_stt_atomic_noeq_comp ru rt re rpost_abs)
                  (elab_comp c)

       | STT_Ghost ->
         RT.equiv (extend_env_l f g)
                  (WT.return_stt_ghost_noeq_comp ru rt re rpost_abs)
                  (elab_comp c)) =

    
    match ctag with
    | STT -> elab_stt_equiv _ c _ _ pre_eq (RT.EQ_Refl _ _)
    | STT_Atomic -> elab_statomic_equiv _ c _ _ pre_eq (RT.EQ_Refl _ _)
    | STT_Ghost -> elab_stghost_equiv _ c _ _ pre_eq (RT.EQ_Refl _ _)  in

  let comp_equiv_eq (_:unit{use_eq == true})
    : (match ctag with
       | STT -> RT.equiv (extend_env_l f g)
                         (WT.return_stt_comp ru rt re rpost_abs x)
                         (elab_comp c)
       | STT_Atomic ->
          RT.equiv (extend_env_l f g)
                   (WT.return_stt_atomic_comp ru rt re rpost_abs x)
                   (elab_comp c)
       | STT_Ghost ->
          RT.equiv (extend_env_l f g)
                   (WT.return_stt_ghost_comp ru rt re rpost_abs x)
                   (elab_comp c)) =
    
    assert (elab_term (close_term' (Tm_Star (open_term' post (null_var x) 0)
                                            (Tm_Pure (mk_eq2_prop u t (null_var x) e))) x 0) ==
            RT.open_or_close_term' (elab_term (Tm_Star (open_term' post (null_var x) 0)
                                                       (Tm_Pure (mk_eq2_prop u t (null_var x) e))))
                                   (RT.CloseVar x) 0);
    let elab_c_post =
      mk_abs rt R.Q_Explicit
        (RT.open_or_close_term'
           (mk_star
              (RT.open_or_close_term' rpost (RT.OpenWith rx_tm) 0)
              (PReflUtil.mk_pure (PReflUtil.mk_eq2 ru rt rx_tm re))) (RT.CloseVar x) 0) in

    let post_body_eq
      : RT.equiv (extend_env_l f g)
                 (mk_star
                    (R.pack_ln (R.Tv_App rpost_abs (rx_tm, R.Q_Explicit)))
                    (PReflUtil.mk_pure (PReflUtil.mk_eq2 ru rt rx_tm re)))
                 (mk_star
                    (RT.open_or_close_term' rpost (RT.OpenWith rx_tm) 0)
                    (PReflUtil.mk_pure (PReflUtil.mk_eq2 ru rt rx_tm re)))
      = mk_star_equiv _ _ _ _ _ (RT.EQ_Beta _ rt _ _ _) (RT.EQ_Refl _ _) in

    let post_eq
      : RT.equiv (extend_env_l f g)
                 (WT.return_post_with_eq ru rt re rpost_abs x)
                 elab_c_post
      = RT.equiv_abs rt R.Q_Explicit x post_body_eq in

    match ctag with
    | STT ->
      assert (elab_comp c == mk_stt_comp ru rt elab_c_pre elab_c_post);
      elab_stt_equiv _ c _ _ pre_eq post_eq
    | STT_Atomic ->
      assert (elab_comp c == mk_stt_atomic_comp ru rt emp_inames_tm elab_c_pre elab_c_post);
      elab_statomic_equiv _ c _ _ pre_eq post_eq
    | STT_Ghost ->
      assert (elab_comp c == mk_stt_ghost_comp ru rt emp_inames_tm elab_c_pre elab_c_post);
      elab_stghost_equiv _ c _ _ pre_eq post_eq
  in
  match ctag, use_eq with
  | STT, true ->
    let d = WT.return_stt_typing x rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.ST_Equiv _ _ _ (comp_equiv_eq ()))
  | STT, false ->
    let d = WT.return_stt_noeq_typing rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.ST_Equiv _ _ _ (comp_equiv_noeq ()))
  | STT_Atomic, true ->
    let d = WT.return_stt_atomic_typing x rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.ST_Equiv _ _ _ (comp_equiv_eq ()))
  | STT_Atomic, false ->
    let d = WT.return_stt_atomic_noeq_typing rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.ST_Equiv _ _ _ (comp_equiv_noeq ()))
  | STT_Ghost, true ->
    let d = WT.return_stt_ghost_typing x rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.ST_Equiv _ _ _ (comp_equiv_eq ()))
  | STT_Ghost, false ->
    let d = WT.return_stt_ghost_noeq_typing rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.ST_Equiv _ _ _ (comp_equiv_noeq ()))
#pop-options
