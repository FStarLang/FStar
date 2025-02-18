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

module Pulse.Soundness.Exists

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module WT = Pulse.Lib.Core.Typing
module FV = Pulse.Typing.FV

let intro_exists_soundness
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_IntroExists? d })
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c)) =

  let t0 = t in
  let T_IntroExists _ u b p e t_typing p_typing e_typing = d in
  let rt = b.binder_ty in
  let rt_typing : RT.tot_typing _ rt (R.pack_ln (R.Tv_Type u)) =
      tot_typing_soundness t_typing in
  let rp_typing
      : RT.tot_typing _
          (mk_exists u rt (mk_abs rt R.Q_Explicit p)) slprop_tm =
      tot_typing_soundness p_typing in
  let rp_typing
      : RT.tot_typing _
          (mk_abs rt R.Q_Explicit p)
          (mk_arrow (rt, R.Q_Explicit) slprop_tm) =
        WT.exists_inversion rp_typing
  in
  let re_typing : RT.ghost_typing _ e _ =
    ghost_typing_soundness e_typing
  in

  let d = WT.intro_exists_typing rt_typing rp_typing re_typing in
  assume (RT.ln' p 0);
  assume (RT.ln e);
  RT.T_Sub _ _ _ _ d
    (RT.Relc_typ _ _ _ _ _
       (RT.Rel_equiv _ _ _ _
          (elab_stghost_equiv _ c _ _
             (RT.Rel_beta _ rt R.Q_Explicit p e) (RT.Rel_refl _ _ _))))

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
  let rt_typing = tot_typing_soundness t_typing in
  let rp_typing
    : RT.tot_typing (elab_env g)
                    (mk_exists u t
                       (mk_abs t R.Q_Explicit p))
                slprop_tm
    = tot_typing_soundness p_typing in
  let rp_typing = WT.exists_inversion rp_typing in

  FV.st_typing_freevars_inv d x;
  assert (~ (Set.mem x (freevars t)));
  assert (~ (Set.mem x (freevars p)));

  let x_tm = tm_var {nm_index=x;nm_ppname=ppname_default} in
  let rx_tm = R.pack_ln (R.Tv_Var (R.pack_namedv (RT.make_namedv x))) in

  let rreveal_x = Pulse.Reflection.Util.mk_reveal u t rx_tm in

  let post_eq =
    assume (RT.ln' p 0);
    assume (RT.ln rreveal_x);
    RT.equiv_abs_close (Pulse.Reflection.Util.mk_erased u t) R.Q_Explicit x
      (RT.Rel_beta (RT.extend_env (elab_env g) _ _) t R.Q_Explicit p rreveal_x)  in

  let comp_equiv = elab_stghost_equiv (elab_env g) c _ _ (RT.Rel_refl _ _ _) post_eq in
  let d = WT.elim_exists_typing #_ #u x rt_typing rp_typing in
  RT.T_Sub _ _ _ _ d
    (RT.Relc_typ _ _ _ _ _
       (RT.Rel_equiv _ _ _ _ comp_equiv))
#pop-options
