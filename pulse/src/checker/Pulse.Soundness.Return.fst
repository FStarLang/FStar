(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Soundness.Return

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module R = FStar.Reflection.V2

module PReflUtil = Pulse.Reflection.Util
module WT = Pulse.Lib.Core.Typing

#push-options "--z3rlimit_factor 8 --split_queries no --fuel 4 --ifuel 2"
let return_soundness
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_Return? d})
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c)) =

  let T_Return _ ctag use_eq u t e post x t_typing e_typing post_typing = d in
  let rpost_abs = mk_abs t R.Q_Explicit post in
  let rt_typing : RT.tot_typing _ t (R.pack_ln (R.Tv_Type u)) =
    tot_typing_soundness t_typing in
  let re_typing : RT.typing _ e (eff_of_ctag ctag, t) =
    match ctag with
    | STT_Ghost -> ghost_typing_soundness e_typing
    | _ -> tot_typing_soundness e_typing in
  let rpost_abs_typing
    : RT.tot_typing _ rpost_abs
                      (mk_arrow (t, R.Q_Explicit) slprop_tm) =
    mk_t_abs_tot g #_ #None ppname_default t_typing post_typing in
  
  let rx_tm = RT.var_as_term x in
  let elab_c_pre = RT.subst_term post [ RT.DT 0 e ] in
  let pre_eq
    : RT.equiv (elab_env g)
               (R.pack_ln (R.Tv_App rpost_abs (e, R.Q_Explicit)))
               elab_c_pre
    = assume (RT.ln' post 0);
      assume (RT.ln e);
      RT.Rel_beta (elab_env g) t R.Q_Explicit post e in
  
  let comp_equiv_noeq (_:unit{use_eq == false})
    : (match ctag with
       | STT -> RT.equiv (elab_env g)
                         (WT.return_stt_noeq_comp u t e rpost_abs)
                         (elab_comp c)
       | STT_Atomic ->
         RT.equiv (elab_env g)
                  (WT.return_stt_atomic_noeq_comp u t e rpost_abs)
                  (elab_comp c)

       | STT_Ghost ->
         RT.equiv (elab_env g)
                  (WT.return_stt_ghost_noeq_comp u t e rpost_abs)
                  (elab_comp c)) =

    
    match ctag with
    | STT -> elab_stt_equiv _ c _ _ pre_eq (RT.Rel_refl _ _ _)
    | STT_Atomic -> elab_statomic_equiv _ c _ _ pre_eq (RT.Rel_refl _ _ _)
    | STT_Ghost -> elab_stghost_equiv _ c _ _ pre_eq (RT.Rel_refl _ _ _)  in

  let comp_equiv_eq (_:unit{use_eq == true})
    : GTot (match ctag with
       | STT -> RT.equiv (elab_env g)
                         (WT.return_stt_comp u t e rpost_abs x)
                         (elab_comp c)
       | STT_Atomic ->
          RT.equiv (elab_env g)
                   (WT.return_stt_atomic_comp u t e rpost_abs x)
                   (elab_comp c)
       | STT_Ghost ->
          RT.equiv (elab_env g)
                   (WT.return_stt_ghost_comp u t e rpost_abs x)
                   (elab_comp c)) =
    
    assert (close_term' (tm_star (open_term' post (null_var x) 0)
                                 (tm_pure (mk_eq2 u t (null_var x) e))) x 0 ==
            RT.subst_term (tm_star (open_term' post (null_var x) 0)
                                   (tm_pure (mk_eq2 u t (null_var x) e)))
                          [ RT. ND x 0 ]);
    let elab_c_post =
      mk_abs t R.Q_Explicit
        (RT.subst_term
           (mk_star
              (RT.subst_term post [ RT.DT 0 rx_tm ])
              (PReflUtil.mk_pure (PReflUtil.mk_eq2 u t rx_tm e)))
           [ RT.ND x 0 ]) in

    let post_body_eq
      : RT.equiv (RT.extend_env (elab_env g) x _)
                 (mk_star
                    (R.pack_ln (R.Tv_App rpost_abs (rx_tm, R.Q_Explicit)))
                    (PReflUtil.mk_pure (PReflUtil.mk_eq2 u t rx_tm e)))
                 (mk_star
                    (RT.subst_term post [ RT.DT 0 rx_tm ])
                    (PReflUtil.mk_pure (PReflUtil.mk_eq2 u t rx_tm e)))
      = mk_star_equiv _ _ _ _ _ (RT.Rel_beta _ t _ _ _) (RT.Rel_refl _ _ _) in

    let post_eq
      : RT.equiv (elab_env g)
                 (WT.return_post_with_eq u t e rpost_abs x)
                 elab_c_post
      = RT.equiv_abs_close t R.Q_Explicit x post_body_eq in

    match ctag with
    | STT ->
      assert (elab_comp c == mk_stt_comp u t elab_c_pre elab_c_post);
      elab_stt_equiv _ c _ _ pre_eq post_eq
    | STT_Atomic ->
      assert (elab_comp c == mk_stt_atomic_comp WT.neutral_fv u t tm_emp_inames elab_c_pre elab_c_post);
      elab_statomic_equiv _ c _ _ pre_eq post_eq
    | STT_Ghost ->
      assert (elab_comp c == mk_stt_ghost_comp u t tm_emp_inames elab_c_pre elab_c_post);
      elab_stghost_equiv _ c _ _ pre_eq post_eq
  in
  match ctag, use_eq with
  | STT, true ->
    let d = WT.return_stt_typing x rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.Relc_typ _ _ _ _ _ (RT.Rel_equiv _ _ _ _ (comp_equiv_eq ())))
  | STT, false ->
    let d = WT.return_stt_noeq_typing rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.Relc_typ _ _ _ _ _ (RT.Rel_equiv _ _ _ _ (comp_equiv_noeq ())))
  | STT_Atomic, true ->
    let d = WT.return_stt_atomic_typing x rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.Relc_typ _ _ _ _ _ (RT.Rel_equiv _ _ _ _ (comp_equiv_eq ())))
  | STT_Atomic, false ->
    let d = WT.return_stt_atomic_noeq_typing rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.Relc_typ _ _ _ _ _ (RT.Rel_equiv _ _ _ _ (comp_equiv_noeq ())))
  | STT_Ghost, true ->
    let d = WT.return_stt_ghost_typing x rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.Relc_typ _ _ _ _ _ (RT.Rel_equiv _ _ _ _ (comp_equiv_eq ())))
  | STT_Ghost, false ->
    let d = WT.return_stt_ghost_noeq_typing rt_typing re_typing rpost_abs_typing in
    RT.T_Sub _ _ _ _ d (RT.Relc_typ _ _ _ _ _ (RT.Rel_equiv _ _ _ _ (comp_equiv_noeq ())))
#pop-options
