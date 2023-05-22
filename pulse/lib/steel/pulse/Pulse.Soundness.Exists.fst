module Pulse.Soundness.Exists

module R = FStar.Reflection
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module WT = Pulse.Steel.Wrapper.Typing
module LN = Pulse.Typing.LN
module FV = Pulse.Typing.FV

#push-options "--fuel 4 --ifuel 1"
let intro_exists_erased_soundness
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_IntroExistsErased? d})
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c)) =
  let t0 = t in
  let T_IntroExistsErased _ u t p e t_typing p_typing e_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let rp = elab_term p in
  let re = elab_term e in
  let rt_typing : RT.tot_typing _ rt (R.pack_ln (R.Tv_Type ru)) =
      tot_typing_soundness t_typing in

  let rp_typing
      : RT.tot_typing _
          (mk_exists ru rt (mk_abs rt R.Q_Explicit rp)) vprop_tm =
      tot_typing_soundness p_typing
  in
  let rp_typing
      : RT.tot_typing _
          (mk_abs rt R.Q_Explicit rp)
          (mk_arrow (rt, R.Q_Explicit) vprop_tm) =
        WT.exists_inversion rp_typing
  in
  let re_typing : RT.tot_typing _ re _ =
      tot_typing_soundness e_typing
  in
  let reveal_re = elab_term (mk_reveal u t e) in

  let d = WT.intro_exists_erased_typing rt_typing rp_typing re_typing in
  assume (RT.ln' rp 0);
  assume (RT.ln reveal_re);
  RT.T_Sub _ _ _ _ d
    (RT.Relc_typ _ _ _ _ _
       (RT.Rel_equiv _ _ _ _
          (elab_stghost_equiv _ c _ _
             (RT.EQ_Beta _ rt R.Q_Explicit rp reveal_re) (RT.EQ_Refl _ _))))

let intro_exists_soundness
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_IntroExists? d })
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c)) =

  let t0 = t in
  let T_IntroExists _ u t p e t_typing p_typing e_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let rp = elab_term p in
  let re = elab_term e in
  let rt_typing : RT.tot_typing _ rt (R.pack_ln (R.Tv_Type ru)) =
      tot_typing_soundness t_typing in
  let rp_typing
      : RT.tot_typing _
          (mk_exists ru rt (mk_abs rt R.Q_Explicit rp)) vprop_tm =
      tot_typing_soundness p_typing in
  let rp_typing
      : RT.tot_typing _
          (mk_abs rt R.Q_Explicit rp)
          (mk_arrow (rt, R.Q_Explicit) vprop_tm) =
        WT.exists_inversion rp_typing
  in
  let re_typing : RT.tot_typing _ re _ =
      tot_typing_soundness e_typing
  in

  let d = WT.intro_exists_typing rt_typing rp_typing re_typing in
  assume (RT.ln' rp 0);
  assume (RT.ln re);
  RT.T_Sub _ _ _ _ d
    (RT.Relc_typ _ _ _ _ _
       (RT.Rel_equiv _ _ _ _
          (elab_stghost_equiv _ c _ _
             (RT.EQ_Beta _ rt R.Q_Explicit rp re) (RT.EQ_Refl _ _))))
#pop-options

#push-options "--z3rlimit_factor 4 --fuel 4 --ifuel 2"
let elim_exists_soundness
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_ElimExists? d})
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c)) =

  let T_ElimExists _ u t p x t_typing p_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let rp = elab_term p in
  let rt_typing = tot_typing_soundness t_typing in
  let rp_typing
    : RT.tot_typing (elab_env g)
                    (mk_exists ru (elab_term t)
                       (mk_abs (elab_term t) R.Q_Explicit (elab_term p)))
                vprop_tm
    = tot_typing_soundness p_typing in
  let rp_typing = WT.exists_inversion rp_typing in

  FV.st_typing_freevars_inv d x;
  assert (~ (Set.mem x (freevars t)));
  assert (~ (Set.mem x (freevars p)));

  let x_tm = Tm_Var {nm_index=x;nm_ppname=RT.pp_name_default;nm_range=Range.range_0} in
  let rx_tm = R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv x))) in

  let rreveal_x = Pulse.Reflection.Util.mk_reveal ru rt rx_tm in

  // somehow can't do without this assertion
  assert (elab_term (mk_reveal u t x_tm) ==
          Pulse.Reflection.Util.mk_reveal ru rt rx_tm);

  let post_eq =
    assume (RT.ln' rp 0);
    assume (RT.ln rreveal_x);
    RT.equiv_abs_close (Pulse.Reflection.Util.mk_erased ru rt) R.Q_Explicit x
      (RT.EQ_Beta (RT.extend_env (elab_env g) _ _) rt R.Q_Explicit rp rreveal_x)  in

  let comp_equiv = elab_stghost_equiv (elab_env g) c _ _ (RT.EQ_Refl _ _) post_eq in
  let d = WT.elim_exists_typing x rt_typing rp_typing in
  RT.T_Sub _ _ _ _ d
    (RT.Relc_typ _ _ _ _ _
       (RT.Rel_equiv _ _ _ _ comp_equiv))
#pop-options
