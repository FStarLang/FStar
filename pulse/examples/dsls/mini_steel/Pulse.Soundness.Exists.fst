module Pulse.Soundness.Exists

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
module FV = Pulse.Typing.FV

#push-options "--fuel 4 --ifuel 1"
let intro_exists_erased_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_IntroExistsErased? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =
  let t0 = t in
  let T_IntroExistsErased _ u t p e t_typing p_typing e_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let rp = elab_term p in
  let re = elab_term e in
  let rt_typing : RT.typing _ rt (R.pack_ln (R.Tv_Type ru)) =
      tot_typing_soundness t_typing in

  let rp_typing
      : RT.typing _
                  (mk_exists ru rt (mk_abs rt R.Q_Explicit rp)) vprop_tm =
      tot_typing_soundness p_typing
  in
  let rp_typing
      : RT.typing _
                  (mk_abs rt R.Q_Explicit rp)
                  (mk_arrow (rt, R.Q_Explicit) vprop_tm) =
        WT.exists_inversion rp_typing
  in
  let re_typing : RT.typing _ re _ =
      tot_typing_soundness e_typing
  in
  let reveal_re = elab_term (mk_reveal u t e) in

  // reveal_re is ln
  LN.tot_typing_ln e_typing;
  elab_ln (mk_reveal u t e) (-1);

  //rp is (ln' 0)
  LN.tot_typing_ln p_typing;
  elab_ln p 0;
  
  RT.beta_reduction rt R.Q_Explicit rp reveal_re;    

  WT.intro_exists_erased_typing rt_typing rp_typing re_typing

let intro_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_IntroExists? d })
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let t0 = t in
  let T_IntroExists _ u t p e t_typing p_typing e_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let rp = elab_term p in
  let re = elab_term e in
  let rt_typing : RT.typing _ rt (R.pack_ln (R.Tv_Type ru)) =
      tot_typing_soundness t_typing in
  let rp_typing
      : RT.typing _
                  (mk_exists ru rt (mk_abs rt R.Q_Explicit rp)) vprop_tm =
      tot_typing_soundness p_typing in
  let rp_typing
      : RT.typing _
                  (mk_abs rt R.Q_Explicit rp)
                  (mk_arrow (rt, R.Q_Explicit) vprop_tm) =
        WT.exists_inversion rp_typing
  in
  let re_typing : RT.typing _ re _ =
      tot_typing_soundness e_typing
  in

  // re is ln
  LN.tot_typing_ln e_typing;
  elab_ln e (-1);

  //rp is (ln' 0)
  LN.tot_typing_ln p_typing;
  elab_ln p 0;

  RT.beta_reduction rt R.Q_Explicit rp re;

  WT.intro_exists_typing rt_typing rp_typing re_typing
#pop-options

#push-options "--z3rlimit_factor 8 --fuel 4 --ifuel 2"
let elim_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_ElimExists? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_ElimExists _ u t p x t_typing p_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let rp = elab_term p in
  let rt_typing = tot_typing_soundness t_typing in
  let rp_typing
    : RT.typing (extend_env_l f g)
                (mk_exists ru (elab_term t)
                   (mk_abs (elab_term t) R.Q_Explicit (elab_term p)))
                vprop_tm
    = tot_typing_soundness p_typing in
  let rp_typing = WT.exists_inversion rp_typing in

  FV.st_typing_freevars_inv d x;
  assert (~ (Set.mem x (freevars t)));
  assert (~ (Set.mem x (freevars p)));

  let x_tm = Tm_Var {nm_index=x;nm_ppname=RT.pp_name_default} in
  let rx_tm = R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv x tun))) in
  let rx_bv = R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv 0 tun))) in

  // rt is ln
  LN.tot_typing_ln t_typing;
  elab_ln t (-1);

  //rp is (ln' 0)
  LN.tot_typing_ln p_typing;
  elab_ln p 0;

  calc (==) {
    elab_term (close_term' (open_term' p (mk_reveal u t x_tm) 0) x 0);
       (==) {
               RT.beta_reduction rt R.Q_Explicit rp (Pulse.Reflection.Util.mk_reveal ru rt rx_tm)
            }
    WT.elim_exists_post_body ru rt (mk_abs rt R.Q_Explicit rp) x;
  };
  WT.elim_exists_typing x rt_typing rp_typing
#pop-options
