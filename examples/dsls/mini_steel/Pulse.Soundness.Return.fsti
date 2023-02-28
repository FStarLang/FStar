module Pulse.Soundness.Return

open FStar.Reflection
open Refl.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Typing
open Pulse.Soundness.Common

module EPure = Pulse.Elaborate.Pure
module RT = Refl.Typing


let return_post_with_eq (u:universe) (a:term) (x:term) (p:term) : term =
  let eq2_tm =
    let t = pack_ln (Tv_UInst (pack_fv (mk_steel_wrapper_lid "eq2_prop")) [u]) in
    let t = pack_ln (Tv_App t (a, Q_Implicit)) in
    let t = pack_ln (Tv_App t (bound_var 0, Q_Explicit)) in
    pack_ln (Tv_App t (x, Q_Explicit)) in

  let p_app_0 = pack_ln (Tv_App p (bound_var 0, Q_Explicit)) in
  
  let star_tm =
    let t = pack_ln (Tv_FVar (pack_fv star_lid)) in
    let t = pack_ln (Tv_App t (p_app_0, Q_Explicit)) in
    pack_ln (Tv_App t (eq2_tm, Q_Explicit)) in

  mk_abs a Q_Explicit star_tm
  
val return_stt_typing
  (#f:stt_env)
  (#g:env)
  (#u:universe)
  (#a:term)
  (#x:term)
  (#p:term)
  (a_typing:RT.typing (extend_env_l f g) a (pack_ln (Tv_Type u)))
  (x_typing:RT.typing (extend_env_l f g) x a)
  (p_typing:RT.typing (extend_env_l f g) p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing (extend_env_l f g)
                    (mk_stt_return u a x p)
                    (mk_stt_comp u a
                       (pack_ln (Tv_App p (x, Q_Explicit)))
                       (return_post_with_eq u a x p)))

val return_stt_noeq_typing
  (#f:stt_env)
  (#g:env)
  (#u:universe)
  (#a:term)
  (#x:term)
  (#p:term)
  (a_typing:RT.typing (extend_env_l f g) a (pack_ln (Tv_Type u)))
  (x_typing:RT.typing (extend_env_l f g) x a)
  (p_typing:RT.typing (extend_env_l f g) p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing (extend_env_l f g)
                    (mk_stt_return u a x p)
                    (mk_stt_comp u a (pack_ln (Tv_App p (x, Q_Explicit))) p))

                      
  // : GTot (RT.typing (extend_env_l f g)
  //                   (mk_stt_admit u a p q)
  //                   (mk_stt_comp u a p q))



// val elab_return_typing (#f:stt_env)
//                        (#g:env)
//                        (#u:universe)
//                        (#ty:term)
//                        (#v:term)
//                        (ty_typing: universe_of f g ty u)
//                        (v_typing: tot_typing f g v ty)
//   : GTot (RT.typing (extend_env_l f g)
//                     (mk_return (elab_universe u) (elab_term ty) (elab_term v))
//                     (elab_comp (return_comp u ty v)))


// val elab_return_noeq_typing (#f:stt_env)
//                             (#g:env)
//                             (#u:universe)
//                             (#ty:term)
//                             (#r:R.term)
//                             (ty_typing: universe_of f g ty u)
//                             (r_typing: RT.typing (extend_env_l f g) r (elab_term ty))
//   : GTot (RT.typing (extend_env_l f g)
//                     (mk_return_noeq (elab_universe u) (elab_term ty) r)
//                     (elab_comp (return_comp_noeq u ty)))
