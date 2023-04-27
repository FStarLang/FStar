module Pulse.Steel.Wrapper.Typing

open FStar.Reflection
open Pulse.Reflection.Util

module RT = FStar.Reflection.Typing

let return_post_with_eq (u:universe) (a:term) (e:term) (p:term) (x:var) : term =
  let x_tm = RT.var_as_term x in
  let eq2_tm = mk_eq2 u a x_tm e in
  let p_app_x = pack_ln (Tv_App p (x_tm, Q_Explicit)) in  
  let star_tm = mk_star p_app_x (mk_pure eq2_tm) in
  mk_abs a Q_Explicit (RT.open_or_close_term' star_tm (RT.CloseVar x) 0)

let return_stt_comp (u:universe) (a:term) (e:term) (p:term) (x:var) : term =
  mk_stt_comp u a
    (pack_ln (Tv_App p (e, Q_Explicit)))
    (return_post_with_eq u a e p x)

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
                    (return_stt_comp u a e p x))

let return_stt_noeq_comp (u:universe) (a:term) (x:term) (p:term) : term =
  mk_stt_comp u a (pack_ln (Tv_App p (x, Q_Explicit))) p

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
                    (mk_stt_return_noeq u a x p)
                    (return_stt_noeq_comp u a x p))

let return_stt_atomic_comp (u:universe) (a:term) (e:term) (p:term) (x:var) : term =
  mk_stt_atomic_comp u a emp_inames_tm
    (pack_ln (Tv_App p (e, Q_Explicit)))
    (return_post_with_eq u a e p x)

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
                    (return_stt_atomic_comp u a e p x))

let return_stt_atomic_noeq_comp (u:universe) (a:term) (x:term) (p:term) : term =
  mk_stt_atomic_comp u a emp_inames_tm (pack_ln (Tv_App p (x, Q_Explicit))) p

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
                    (return_stt_atomic_noeq_comp u a x p))

let return_stt_ghost_comp (u:universe) (a:term) (e:term) (p:term) (x:var) : term =
  mk_stt_ghost_comp u a emp_inames_tm
    (pack_ln (Tv_App p (e, Q_Explicit)))
    (return_post_with_eq u a e p x)

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
                    (return_stt_ghost_comp u a e p x))

let return_stt_ghost_noeq_comp (u:universe) (a:term) (x:term) (p:term) : term =
  mk_stt_ghost_comp u a emp_inames_tm (pack_ln (Tv_App p (x, Q_Explicit))) p

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
                    (return_stt_ghost_noeq_comp u a x p))


(*

 g |- inv  : bool -> vprop
 g |- cond : stt<0> bool (exists_ inv) inv
 g |- body : stt<0> unit (inv true) (fun _ -> exists_ inv)
 -------------------------------------------------------------------------
 g |- while inv cond body : stt<0> unit (exists_ inv) (fun _ -> inv false)

*)

val while_typing
  (#g:env)
  (#inv:term)
  (#cond:term)
  (#body:term)
  (inv_typing:RT.typing g
                     inv
                     (mk_arrow (bool_tm, Q_Explicit) vprop_tm))
  (cond_typing:RT.typing g
                      cond
                      (mk_stt_comp uzero bool_tm (mk_exists uzero bool_tm inv) inv))
  (body_typing:RT.typing g
                      body
                      (mk_stt_comp uzero unit_tm
                         (pack_ln (Tv_App inv (true_tm, Q_Explicit)))
                         (mk_abs unit_tm Q_Explicit (mk_exists uzero bool_tm inv))))
  : RT.typing g
           (mk_while inv cond body)
           (mk_stt_comp uzero unit_tm (mk_exists uzero bool_tm inv)
              (mk_abs unit_tm Q_Explicit (pack_ln (Tv_App inv (false_tm, Q_Explicit)))))

let par_post (u:universe) (aL aR:term) (postL postR:term) (x:var) : term =
  let x_tm = RT.var_as_term x in
  let postL = pack_ln (Tv_App postL (mk_fst u u aL aR x_tm, Q_Explicit)) in
  let postR = pack_ln (Tv_App postR (mk_snd u u aL aR x_tm, Q_Explicit)) in
  let post = mk_star postL postR in
  RT.open_or_close_term' post (RT.CloseVar x) 0

val par_typing
  (#g:env)
  (#u:universe)
  (#aL #aR:term)
  (#preL #postL:term)
  (#preR #postR:term)
  (#eL #eR:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (aL_typing:RT.typing g aL (pack_ln (Tv_Type u)))
  (aR_typing:RT.typing g aR (pack_ln (Tv_Type u)))
  (preL_typing:RT.typing g preL vprop_tm)
  (postL_typing:RT.typing g postL (mk_arrow (aL, Q_Explicit) vprop_tm))
  (preR_typing:RT.typing g preR vprop_tm)
  (postR_typing:RT.typing g postR (mk_arrow (aR, Q_Explicit) vprop_tm))
  (eL_typing:RT.typing g eL (mk_stt_comp u aL preL postL))
  (eR_typing:RT.typing g eR (mk_stt_comp u aR preR postR))

  : GTot (RT.typing g
                    (mk_par u aL aR preL postL preR postR eL eR)
                    (mk_stt_comp u (mk_tuple2 u u aL aR)
                       (mk_star preL preR)
                       (mk_abs (mk_tuple2 u u aL aR) Q_Explicit (par_post u aL aR postL postR x))))

val exists_inversion
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (e_typing:RT.typing g
                      (mk_exists u a p)
                      vprop_tm)
  : GTot (RT.typing g
                    p
                   (mk_arrow (a, Q_Explicit) vprop_tm))

(*

 g |- a : Type u
 g |- p : a -> vprop
 ----------------------------------------------------------------
 g |- elim_exists<u> #a p : stt_ghost<u> a empty (exists_<u> p) (fun x -> p (reveal x))

*)

let elim_exists_post_body (u:universe) (a:term) (p:term) (x:var) =
  let x_tm = RT.var_as_term x in
  let reveal_x = mk_reveal u a x_tm in
  let post = pack_ln (Tv_App p (reveal_x, Q_Explicit)) in
  RT.open_or_close_term' post (RT.CloseVar x) 0

let elim_exists_post (u:universe) (a:term) (p:term) (x:var) =
  let erased_a = mk_erased u a in
  mk_abs erased_a Q_Explicit (elim_exists_post_body u a p x)

val elim_exists_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))
  : GTot (RT.typing g
                 (mk_elim_exists u a p)
                 (mk_stt_ghost_comp
                    u
                    (mk_erased u a) 
                    emp_inames_tm
                    (mk_exists u a p)
                    (elim_exists_post u a p x)))

(*

 g |- a : Type u
 g |- p : a -> vprop
 g |- e : vprop
 -------------------------------------------------------------------------
 g |- intro_exists<u> #a p e : stt_ghost<0> unit empty (p e) (fun _ -> exists_ p)

*)
val intro_exists_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#e:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))
  (e_typing:RT.typing g e a)
  : GTot (RT.typing g
                 (mk_intro_exists u a p e)
                 (mk_stt_ghost_comp uzero unit_tm emp_inames_tm
                    (pack_ln (Tv_App p (e, Q_Explicit)))
                    (mk_abs unit_tm Q_Explicit (mk_exists u a p))))

(*

 g |- a : Type u
 g |- p : a -> vprop
 g |- e : vprop
 -------------------------------------------------------------------------
 g |- intro_exists<u> #a p e : stt_ghost<0> unit empty (p e) (fun _ -> exists_ p)

*)
val intro_exists_erased_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#e:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p (mk_arrow (a, Q_Explicit) vprop_tm))
  (e_typing:RT.typing g e (mk_erased u a))
  : GTot (RT.typing g
                 (mk_intro_exists_erased u a p e)
                 (mk_stt_ghost_comp uzero unit_tm emp_inames_tm
                    (pack_ln (Tv_App p (mk_reveal u a e, Q_Explicit)))
                    (mk_abs unit_tm Q_Explicit (mk_exists u a p))))

(*

 g |- a : Type u
 g |- p : vprop
 g |- q : a -> vprop
 ------------------------------------------
 g |- stt_admit a p q : stt a p q

*)

val stt_admit_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#q:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p vprop_tm)
  (q_typing:RT.typing g q (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_admit u a p q)
                    (mk_stt_comp u a p q))
               
val stt_atomic_admit_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#q:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p vprop_tm)
  (q_typing:RT.typing g q (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_atomic_admit u a p q)
                    (mk_stt_atomic_comp u a emp_inames_tm p q))

val stt_ghost_admit_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#q:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p vprop_tm)
  (q_typing:RT.typing g q (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_ghost_admit u a p q)
                    (mk_stt_ghost_comp u a emp_inames_tm p q))

val rewrite_typing
  (#g:env)
  (#p:term)
  (#q:term)
  (p_typing:RT.typing g p vprop_tm)
  (q_typing:RT.typing g q vprop_tm)
  (equiv:RT.typing g (`()) (stt_vprop_equiv p q))

		: GTot (RT.typing g
                      (mk_rewrite p q)
                      (mk_stt_ghost_comp
                        uzero
                        unit_tm
                        emp_inames_tm
                        p
                        (mk_abs unit_tm Q_Explicit q)))

let with_local_bodypost_body (post:term) (a:term) (x:var) : term =
  let x_tm = RT.var_as_term x in
  // post x
  let post_app = pack_ln (Tv_App post (x_tm, Q_Explicit)) in
  // exists_ (R.pts_to r full_perm)
  let exists_tm =
    let t = pack_ln (Tv_FVar (pack_fv pts_to_lid)) in
    let t = pack_ln (Tv_App t (a, Q_Implicit)) in
    let t = pack_ln (Tv_App t ((RT.bound_var 1), Q_Explicit)) in
    let t = pack_ln (Tv_App t (full_perm_tm, Q_Explicit)) in
    mk_exists (pack_universe Uv_Zero) a t in
  let star_tm = mk_star post_app exists_tm in
  RT.open_or_close_term' star_tm (RT.CloseVar x) 0

let with_local_bodypost (post:term) (a:term) (ret_t:term) (x:var) : term =
  mk_abs ret_t Q_Explicit (with_local_bodypost_body post a x)


val with_local_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#init:term)
  (#pre:term)
  (#ret_t:term)
  (#post:term)
  (#body:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.typing g a (pack_ln (Tv_Type (pack_universe Uv_Zero))))
  (init_typing:RT.typing g init a)
  (pre_typing:RT.typing g pre vprop_tm)
  (ret_t_typing:RT.typing g ret_t (pack_ln (Tv_Type u)))
  (post_typing:RT.typing g post (mk_arrow (ret_t, Q_Explicit) vprop_tm))
  (body_typing:RT.typing g 
                         body
                         (mk_arrow
                            (mk_ref a, Q_Explicit)
                            (mk_stt_comp u ret_t
                               (mk_star pre (mk_pts_to a (RT.bound_var 0) full_perm_tm init))
                               (with_local_bodypost post a ret_t x))))
  : GTot (RT.typing g (mk_withlocal u a init pre ret_t post body)
                    (mk_stt_comp u ret_t pre post))
