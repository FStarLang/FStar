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

module Pulse.Lib.Core.Typing

open FStar.Reflection.V2
open Pulse.Reflection.Util

module RT = FStar.Reflection.Typing

let return_post_with_eq (u:universe) (a:term) (e:term) (p:term) (x:var) : term =
  let x_tm = RT.var_as_term x in
  let eq2_tm = mk_eq2 u a x_tm e in
  let p_app_x = pack_ln (Tv_App p (x_tm, Q_Explicit)) in  
  let star_tm = mk_star p_app_x (mk_pure eq2_tm) in
  mk_abs a Q_Explicit (RT.subst_term star_tm [ RT.ND x 0 ])

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
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (e_typing:RT.tot_typing g e a)
  (p_typing:RT.tot_typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.tot_typing g
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
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (x_typing:RT.tot_typing g x a)
  (p_typing:RT.tot_typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.tot_typing g
            (mk_stt_return_noeq u a x p)
            (return_stt_noeq_comp u a x p))

let neutral_fv = pack_ln (Tv_FVar (pack_fv neutral_lid))
let return_stt_atomic_comp (u:universe) (a:term) (e:term) (p:term) (x:var) : term =
  mk_stt_atomic_comp neutral_fv u a emp_inames_tm
    (pack_ln (Tv_App p (e, Q_Explicit)))
    (return_post_with_eq u a e p x)

val return_stt_atomic_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#e:term)
  (#p:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (e_typing:RT.tot_typing g e a)
  (p_typing:RT.tot_typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.tot_typing g
            (mk_stt_atomic_return u a e p)
            (return_stt_atomic_comp u a e p x))

let return_stt_atomic_noeq_comp (u:universe) (a:term) (x:term) (p:term) : term =
  mk_stt_atomic_comp neutral_fv u a emp_inames_tm (pack_ln (Tv_App p (x, Q_Explicit))) p

val return_stt_atomic_noeq_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#x:term)
  (#p:term)
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (x_typing:RT.tot_typing g x a)
  (p_typing:RT.tot_typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.tot_typing g
            (mk_stt_atomic_return_noeq u a x p)
            (return_stt_atomic_noeq_comp u a x p))

let return_stt_ghost_comp (u:universe) (a:term) (e:term) (p:term) (x:var) : term =
  mk_stt_ghost_comp u a
    (pack_ln (Tv_App p (e, Q_Explicit)))
    (return_post_with_eq u a e p x)

val return_stt_ghost_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#e:term)
  (#p:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (e_typing:RT.ghost_typing g e a)
  (p_typing:RT.tot_typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.tot_typing g
            (mk_stt_ghost_return u a e p)
            (return_stt_ghost_comp u a e p x))

let return_stt_ghost_noeq_comp (u:universe) (a:term) (x:term) (p:term) : term =
  mk_stt_ghost_comp u a (pack_ln (Tv_App p (x, Q_Explicit))) p

val return_stt_ghost_noeq_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#x:term)
  (#p:term)
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (x_typing:RT.ghost_typing g x a)
  (p_typing:RT.tot_typing g p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.tot_typing g
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
  (inv_typing:RT.tot_typing g
                inv
                (mk_arrow (bool_tm, Q_Explicit) vprop_tm))
  (cond_typing:RT.tot_typing g
                 cond
                 (mk_stt_comp uzero bool_tm (mk_exists uzero bool_tm inv) inv))
  (body_typing:RT.tot_typing g
                 body
                 (mk_stt_comp uzero unit_tm
                    (pack_ln (Tv_App inv (true_tm, Q_Explicit)))
                    (mk_abs unit_tm Q_Explicit (mk_exists uzero bool_tm inv))))
  : RT.tot_typing g
      (mk_while inv cond body)
      (mk_stt_comp uzero unit_tm (mk_exists uzero bool_tm inv)
         (mk_abs unit_tm Q_Explicit (pack_ln (Tv_App inv (false_tm, Q_Explicit)))))

let par_post (u:universe) (aL aR:term) (postL postR:term) (x:var) : term =
  let x_tm = RT.var_as_term x in
  let postL = pack_ln (Tv_App postL (mk_fst u u aL aR x_tm, Q_Explicit)) in
  let postR = pack_ln (Tv_App postR (mk_snd u u aL aR x_tm, Q_Explicit)) in
  let post = mk_star postL postR in
  RT.subst_term post [ RT.ND x 0 ]

val par_typing
  (#g:env)
  (#u:universe)
  (#aL #aR:term)
  (#preL #postL:term)
  (#preR #postR:term)
  (#eL #eR:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (aL_typing:RT.tot_typing g aL (pack_ln (Tv_Type u)))
  (aR_typing:RT.tot_typing g aR (pack_ln (Tv_Type u)))
  (preL_typing:RT.tot_typing g preL vprop_tm)
  (postL_typing:RT.tot_typing g postL (mk_arrow (aL, Q_Explicit) vprop_tm))
  (preR_typing:RT.tot_typing g preR vprop_tm)
  (postR_typing:RT.tot_typing g postR (mk_arrow (aR, Q_Explicit) vprop_tm))
  (eL_typing:RT.tot_typing g eL (mk_stt_comp u aL preL postL))
  (eR_typing:RT.tot_typing g eR (mk_stt_comp u aR preR postR))

  : GTot (RT.tot_typing g
            (mk_par u aL aR preL postL preR postR eL eR)
            (mk_stt_comp u (mk_tuple2 u u aL aR)
               (mk_star preL preR)
               (mk_abs (mk_tuple2 u u aL aR) Q_Explicit (par_post u aL aR postL postR x))))

val exists_inversion
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (e_typing:RT.tot_typing g
              (mk_exists u a p)
              vprop_tm)
  : GTot (RT.tot_typing g
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
  RT.subst_term post [ RT.ND x 0 ]

let elim_exists_post (u:universe) (a:term) (p:term) (x:var) =
  let erased_a = mk_erased u a in
  mk_abs erased_a Q_Explicit (elim_exists_post_body u a p x)

val elim_exists_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.tot_typing g p (mk_arrow (a, Q_Explicit) vprop_tm))
  : GTot (RT.tot_typing g
            (mk_elim_exists u a p)
            (mk_stt_ghost_comp
               u
               (mk_erased u a)
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
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.tot_typing g p (mk_arrow (a, Q_Explicit) vprop_tm))
  (e_typing:RT.ghost_typing g e a)
  : GTot (RT.tot_typing g
            (mk_intro_exists u a p e)
            (mk_stt_ghost_comp uzero unit_tm
               (pack_ln (Tv_App p (e, Q_Explicit)))
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
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.tot_typing g p vprop_tm)
  (q_typing:RT.tot_typing g q (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.tot_typing g
            (mk_stt_admit u a p q)
            (mk_stt_comp u a p q))
               
val stt_atomic_admit_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#q:term)
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.tot_typing g p vprop_tm)
  (q_typing:RT.tot_typing g q (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.tot_typing g
            (mk_stt_atomic_admit u a p q)
            (mk_stt_atomic_comp neutral_fv u a emp_inames_tm p q))

val stt_ghost_admit_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#q:term)
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.tot_typing g p vprop_tm)
  (q_typing:RT.tot_typing g q (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.tot_typing g
            (mk_stt_ghost_admit u a p q)
            (mk_stt_ghost_comp u a p q))

val rewrite_typing
  (#g:env)
  (#p:term)
  (#q:term)
  (p_typing:RT.tot_typing g p vprop_tm)
  (q_typing:RT.tot_typing g q vprop_tm)
  (equiv:RT.tot_typing g (`()) (stt_vprop_equiv p q))

		: GTot (RT.tot_typing g
              (mk_rewrite p q)
              (mk_stt_ghost_comp
              uzero
              unit_tm
              p
              (mk_abs unit_tm Q_Explicit q)))

// mk_star pre (mk_pts_to a (RT.bound_var 0) full_perm_tm init
let with_local_body_pre (pre:term) (a:term) (x:term) (init:term) : term =
  let pts_to : term =
    mk_pts_to a x full_perm_tm init in
  mk_star pre pts_to

//
// post has 0 db index free
//
let with_local_body_post_body (post:term) (a:term) (x:term) : term =
  // exists_ (R.pts_to r full_perm)
  let exists_tm =
    mk_exists (pack_universe Uv_Zero) a
      (mk_abs a Q_Explicit
         (mk_pts_to a x full_perm_tm (RT.bound_var 0))) in
  mk_star post exists_tm

let with_local_body_post (post:term) (a:term) (ret_t:term) (x:term) : term =
  mk_abs ret_t Q_Explicit (with_local_body_post_body post a x)

val with_local_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#init:term)
  (#pre:term)
  (#ret_t:term)
  (#post:term)  // post has db 0 free
  (#body:term)  // body has x free
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type (pack_universe Uv_Zero))))
  (init_typing:RT.tot_typing g init a)
  (pre_typing:RT.tot_typing g pre vprop_tm)
  (ret_t_typing:RT.tot_typing g ret_t (pack_ln (Tv_Type u)))
  (post_typing:RT.tot_typing g (RT.mk_abs ret_t Q_Explicit post)
                               (mk_arrow (ret_t, Q_Explicit) vprop_tm))
  (body_typing:RT.tot_typing (RT.extend_env g x (mk_ref a)) 
                 body
                 (mk_stt_comp u ret_t
                    (with_local_body_pre pre a (RT.var_as_term x) init)
                    (with_local_body_post post a ret_t (RT.var_as_term x))))

  : GTot (RT.tot_typing g (mk_withlocal u a init pre ret_t (RT.mk_abs ret_t Q_Explicit post)
                                                           (RT.mk_abs (mk_ref a) Q_Explicit (RT.close_term body x)))
                          (mk_stt_comp u ret_t pre (mk_abs ret_t Q_Explicit post)))

let with_localarray_body_pre (pre:term) (a:term) (arr:term) (init:term) (len:term) : term =
  let pts_to : term =
    mk_array_pts_to a arr full_perm_tm (mk_seq_create uzero a (mk_szv len) init) in
  let len_vp : term =
    mk_pure (mk_eq2 uzero nat_tm (mk_array_length a arr) (mk_szv len)) in
  mk_star pre (mk_star pts_to len_vp)

//
// post has 0 db index free
//
let with_localarray_body_post_body (post:term) (a:term) (arr:term) : term =
  // exists_ (A.pts_to arr full_perm)
  let exists_tm =
    mk_exists uzero (mk_seq uzero a)
      (mk_abs (mk_seq uzero a) Q_Explicit
         (mk_array_pts_to a arr full_perm_tm (RT.bound_var 0))) in
  mk_star post exists_tm

let with_localarray_body_post (post:term) (a:term) (ret_t:term) (arr:term) : term =
  mk_abs ret_t Q_Explicit (with_localarray_body_post_body post a arr)

val with_localarray_typing
  (#g:env)
  (#u:universe)
  (#a:term)
  (#init:term)
  (#len:term)
  (#pre:term)
  (#ret_t:term)
  (#post:term)  // post has db 0 free
  (#body:term)  // body has x free
  (x:var{None? (RT.lookup_bvar g x)})
  (a_typing:RT.tot_typing g a (pack_ln (Tv_Type (pack_universe Uv_Zero))))
  (init_typing:RT.tot_typing g init a)
  (len_typing:RT.tot_typing g len szt_tm)
  (pre_typing:RT.tot_typing g pre vprop_tm)
  (ret_t_typing:RT.tot_typing g ret_t (pack_ln (Tv_Type u)))
  (post_typing:RT.tot_typing g (RT.mk_abs ret_t Q_Explicit post) (mk_arrow (ret_t, Q_Explicit) vprop_tm))
  (body_typing:RT.tot_typing (RT.extend_env g x (mk_array a))
                             body
                             (mk_stt_comp u ret_t
                                (with_localarray_body_pre pre a (RT.var_as_term x) init len)
                                (with_localarray_body_post post a ret_t (RT.var_as_term x))))
  : GTot (RT.tot_typing g (mk_withlocalarray u a init len pre ret_t (RT.mk_abs ret_t Q_Explicit post)
                                                                    (RT.mk_abs (mk_array a) Q_Explicit (RT.close_term body x)))
                          (mk_stt_comp u ret_t pre (mk_abs ret_t Q_Explicit post)))

val unit_non_informative_witness_typing
  (g:env)
  : GTot (RT.tot_typing g (pack_ln (Tv_FVar (pack_fv unit_non_informative_lid)))
                          (non_informative_witness_rt uzero unit_tm))

val prop_non_informative_witness_typing
  (g:env)
  : GTot (RT.tot_typing g (pack_ln (Tv_FVar (pack_fv prop_non_informative_lid)))
                          (non_informative_witness_rt uzero (pack_ln (Tv_FVar (pack_fv prop_qn)))))

let squash_non_informative_witness_tm (u:universe) (t:term) : term =
  let tm = pack_ln (Tv_UInst (pack_fv squash_non_informative_lid) [u]) in
  pack_ln (Tv_App tm (t, Q_Explicit))

val squash_non_informative_witness_typing
  (#g:env)
  (u:universe)
  (#t:term)
  (t_typing:RT.tot_typing g t (pack_ln (Tv_Type u)))
  : GTot (RT.tot_typing g (squash_non_informative_witness_tm u t)
                          (non_informative_witness_rt uzero (mk_squash u t)))
