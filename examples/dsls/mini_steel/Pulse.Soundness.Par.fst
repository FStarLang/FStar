module Pulse.Soundness.Par

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module R = FStar.Reflection

module WT = Pulse.Steel.Wrapper.Typing


#push-options "--z3rlimit_factor 10 --fuel 8 --ifuel 1"
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

  /////
  let uL = comp_u cL in
  let uR = comp_u cR in
  let aL = comp_res cL in
  let aR = comp_res cR in
  let postL = comp_post cL in
  let postR = comp_post cR in
  let x_tm = term_of_var x in

  // ln proofs for invoking the RT beta reduction
  RT.well_typed_terms_are_ln _ _ _ raL_typing;
  RT.well_typed_terms_are_ln _ _ _ raR_typing;
  RT.well_typed_terms_are_ln _ _ _ rpostL_typing;
  RT.well_typed_terms_are_ln _ _ _ rpostR_typing;

  // calc (==) {
  //   elab_term (par_post uL uR aL aR postL postR x);
  //      (==) { }
  //   RT.open_or_close_term'
  //     (mk_star
  //        (RT.open_or_close_term'
  //           (elab_term postL)
  //           (RT.OpenWith (elab_term (mk_fst uL uR aL aR x_tm))) 0)
  //        (RT.open_or_close_term'
  //           (elab_term postR)
  //           (RT.OpenWith (elab_term (mk_snd uL uR aL aR x_tm))) 0))
  //     (RT.CloseVar x)
  //     0;
  //      (==) { RT.beta_reduction raL R.Q_Explicit
  //               (elab_term postL)
  //               (Pulse.Reflection.Util.mk_fst ru ru raL raR (RT.var_as_term x));
  //             RT.beta_reduction raR R.Q_Explicit
  //               (elab_term postR)
  //               (Pulse.Reflection.Util.mk_snd ru ru raL raR (RT.var_as_term x)) }
  //   WT.par_post ru raL raR rpostL rpostR x;
  // };
  /////
  admit ();

  WT.par_typing x raL_typing raR_typing rpreL_typing rpostL_typing
    rpreR_typing rpostR_typing
    reL_typing reR_typing
#pop-options
