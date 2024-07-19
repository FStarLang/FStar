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

module Pulse.Soundness.Par

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module R = FStar.Reflection.V2

module PReflUtil = Pulse.Reflection.Util
module WT = Pulse.Lib.Core.Typing


#push-options "--z3rlimit_factor 4 --fuel 4 --ifuel 1"
let par_soundness
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_Par? d})
  (soundness: soundness_t d)
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c)) =

  let T_Par _ eL cL eR cR x cL_typing cR_typing eL_typing eR_typing = d in

  let uL = comp_u cL in
  let uR = comp_u cR in
  let raL = comp_res cL in
  let raR = comp_res cR in
  let rpreL = comp_pre cL in
  let rpostL = mk_abs raL R.Q_Explicit (comp_post cL) in
  let rpreR = comp_pre cR in
  let rpostR = mk_abs raR R.Q_Explicit (comp_post cR) in
  let reL = elab_st_typing eL_typing in
  let reR = elab_st_typing eR_typing in

  let reL_typing
    : RT.tot_typing _ reL (elab_comp cL) =
    soundness g eL cL eL_typing in

  let reR_typing
    : RT.tot_typing _ reR (elab_comp cR) =
    soundness g eR cR eR_typing in

  let (raL_typing, rpreL_typing, rpostL_typing)
    : (RT.tot_typing _ raL (R.pack_ln (R.Tv_Type uL)) &
       RT.tot_typing _ rpreL slprop_tm &
       RT.tot_typing _ rpostL (mk_arrow (raL, R.Q_Explicit) slprop_tm)) =

    inversion_of_stt_typing g cL (Comp.comp_typing_soundness g cL _ cL_typing) in

  let (raR_typing, rpreR_typing, rpostR_typing)
    : (RT.tot_typing _ raR (R.pack_ln (R.Tv_Type uR)) &
       RT.tot_typing _ rpreR slprop_tm &
       RT.tot_typing _ rpostR (mk_arrow (raR, R.Q_Explicit) slprop_tm)) =

    inversion_of_stt_typing g cR (Comp.comp_typing_soundness g cR _ cR_typing) in

  let aL = comp_res cL in
  let aR = comp_res cR in
  let postL = comp_post cL in
  let postR = comp_post cR in
  let x_tm = term_of_no_name_var x in
  let rx_tm = RT.var_as_term x in

  elab_open_commute' postL (mk_fst uL uR aL aR x_tm) 0;
  elab_open_commute' postR (mk_snd uL uR aL aR x_tm) 0;

  let post_body_eq : RT.equiv (RT.extend_env (elab_env g) x _)
    (mk_star (R.pack_ln (R.Tv_App rpostL (PReflUtil.mk_fst uL uR raL raR rx_tm, R.Q_Explicit)))
             (R.pack_ln (R.Tv_App rpostR (PReflUtil.mk_snd uL uR raL raR rx_tm, R.Q_Explicit))))
    (tm_star (open_term' postL (mk_fst uL uR aL aR x_tm) 0)
             (open_term' postR (mk_snd uL uR aL aR x_tm) 0))
    = assume (RT.ln' postL 0);
      assume (RT.ln (mk_fst uL uR aL aR x_tm));
      assume (RT.ln' postR 0);
      assume (RT.ln (mk_snd uL uR aL aR x_tm));
      mk_star_equiv _ _ _ _ _
        (RT.Rel_beta _ raL _  postL _)
        (RT.Rel_beta _ raR _ postR _) in

  let post_eq
    : RT.equiv (elab_env g)
               (mk_abs _ R.Q_Explicit _)
               (mk_abs _ R.Q_Explicit _)
    = RT.equiv_abs_close _ _ x post_body_eq in
  assume (uL == uR); //TODO: we should simplify Par to remove the result type altogether
  let d = WT.par_typing x raL_typing raR_typing rpreL_typing rpostL_typing
    rpreR_typing rpostR_typing
    reL_typing reR_typing in
  
  RT.T_Sub _ _ _ _ d
    (RT.Relc_typ _ _ _ _ _
       (RT.Rel_equiv _ _ _ _ (elab_stt_equiv _ c _ _ (RT.Rel_refl _ _ _) post_eq)))
#pop-options
