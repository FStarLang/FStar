module Pulse.Soundness.Return

open FStar.Reflection
open Pulse.Reflection.Util

module RT = Refl.Typing

let return_post_with_eq (u:universe) (a:term) (e:term) (p:term) (x:var) : term =
  let x_tm = RT.var_as_term x in
  let eq2_tm =
    let t = pack_ln (Tv_UInst (pack_fv (mk_steel_wrapper_lid "eq2_prop")) [u]) in
    let t = pack_ln (Tv_App t (a, Q_Implicit)) in
    let t = pack_ln (Tv_App t (x_tm, Q_Explicit)) in
    pack_ln (Tv_App t (e, Q_Explicit)) in

  let p_app_x = pack_ln (Tv_App p (x_tm, Q_Explicit)) in
  
  let star_tm = mk_star p_app_x eq2_tm in

  mk_abs a Q_Explicit (RT.open_or_close_term' star_tm (RT.CloseVar x) 0)

val return_stt_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#e:term)
  (#p:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (e_typing:RT.typing g e a)
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_return u a e p)
                    (mk_stt_comp u a
                       (pack_ln (Tv_App p (e, Q_Explicit)))
                       (return_post_with_eq u a e p x)))

val return_stt_noeq_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#x:term)
  (#p:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (x_typing:RT.typing g x a)
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_return u a x p)
                    (mk_stt_comp u a (pack_ln (Tv_App p (x, Q_Explicit))) p))

val return_stt_atomic_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#e:term)
  (#p:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (e_typing:RT.typing g e a)
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_atomic_return u a e p)
                    (mk_stt_atomic_comp u a emp_inames_tm
                       (pack_ln (Tv_App p (e, Q_Explicit)))
                       (return_post_with_eq u a e p x)))

val return_stt_atomic_noeq_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#x:term)
  (#p:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (x_typing:RT.typing g x a)
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_atomic_return_noeq u a x p)
                    (mk_stt_atomic_comp u a emp_inames_tm (pack_ln (Tv_App p (x, Q_Explicit))) p))

val return_stt_ghost_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#e:term)
  (#p:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (e_typing:RT.typing g e a)
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_ghost_return u a e p)
                    (mk_stt_ghost_comp u a emp_inames_tm
                       (pack_ln (Tv_App p (e, Q_Explicit)))
                       (return_post_with_eq u a e p x)))

val return_stt_ghost_noeq_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#x:term)
  (#p:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (x_typing:RT.typing g x a)
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_ghost_return_noeq u a x p)
                    (mk_stt_ghost_comp u a emp_inames_tm (pack_ln (Tv_App p (x, Q_Explicit))) p))
