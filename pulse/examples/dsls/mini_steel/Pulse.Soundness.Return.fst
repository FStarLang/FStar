module Pulse.Soundness.Return
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

let var_as_bvar_term (v:var) = R.(pack_ln (Tv_BVar (RT.var_as_bv v)))

let emp_tm = R.(pack_ln (Tv_FVar (pack_fv emp_lid)))

let mk_pure t =
  let pure = R.(pack_ln (Tv_FVar (pack_fv pure_lid))) in
  R.mk_app pure [(t, R.Q_Explicit)]

let mk_eq u t v0 v1 = 
  let m_eq2 = R.(pack_ln (Tv_UInst (pack_fv R.eq2_qn) [u])) in
  let eq = R.mk_app m_eq2 [(t, R.Q_Implicit);
                           (v0, R.Q_Explicit);
                           (v1, R.Q_Explicit)] in
  eq
                  
let inst_stt_return (#g:R.env) (#u:R.universe) (#ty #v:R.term)
                    (d_ty:RT.typing g ty (RT.tm_type u))
                    (d_v:RT.typing g v ty)
  : GTot (RT.typing g (mk_return u ty v)
                      (mk_stt_comp u ty
                                     emp_tm
                                     (mk_abs ty R.Q_Explicit (mk_pure (mk_eq u ty (var_as_bvar_term 0) v)))))
   = admit()
                    
#push-options "--query_stats --fuel 4 --ifuel 1"
let elab_return_typing  (#f:stt_env)
                        (#g:env)
                        (#u:universe)
                        (#ty:pure_term)
                        (#v:pure_term)
                        (ty_typing: universe_of f g ty u)
                        (v_typing: tot_typing f g v ty)
  : GTot (RT.typing (extend_env_l f g)
                    (mk_return (elab_universe u) (elab_pure ty) (elab_pure v))
                    (elab_pure_comp (return_comp u ty v)))
  = let ty_typing = tot_typing_soundness ty_typing in
    let v_typing = tot_typing_soundness v_typing in
    let d = inst_stt_return ty_typing v_typing in
    d
#pop-options

let inst_stt_return_noeq (#g:R.env) (#u:R.universe) (#ty #v:R.term)
                          (d_ty:RT.typing g ty (RT.tm_type u))
                          (d_v:RT.typing g v ty)
  : GTot (RT.typing g (mk_return_noeq u ty v)
                      (mk_stt_comp u ty
                                     emp_tm
                                     (mk_abs ty R.Q_Explicit emp_tm)))
   = admit()

#push-options "--query_stats --fuel 4 --ifuel 1"
let elab_return_noeq_typing  (#f:stt_env)
                             (#g:env)
                             (#u:universe)
                             (#ty:pure_term)
                             (#v:R.term)
                             (ty_typing: universe_of f g ty u)
                             (v_typing: RT.typing (extend_env_l f g) v (elab_pure ty))
  : GTot (RT.typing (extend_env_l f g)
                    (mk_return_noeq (elab_universe u) (elab_pure ty) v)
                    (elab_pure_comp (return_comp_noeq u ty)))
  = let ty_typing = tot_typing_soundness ty_typing in
    let d = inst_stt_return_noeq ty_typing v_typing in
    d
#pop-options
