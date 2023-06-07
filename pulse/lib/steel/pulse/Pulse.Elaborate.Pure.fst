module Pulse.Elaborate.Pure
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax.Base

open Pulse.Reflection.Util

let (let!) (f:option 'a) (g: 'a -> option 'b) : option 'b = 
  match f with
  | None -> None
  | Some x -> g x

let elab_qual = function
  | None -> R.Q_Explicit
  | Some Implicit -> R.Q_Implicit

let rec elab_term (top:term)
  : R.term
  = let open R in
    match top with
    | Tm_VProp ->
      pack_ln (Tv_FVar (pack_fv vprop_lid))

    | Tm_Emp ->
      pack_ln (Tv_FVar (pack_fv emp_lid))
      
    | Tm_Pure p ->
      let p = elab_term p in
      let head = pack_ln (Tv_FVar (pack_fv pure_lid)) in
      pack_ln (Tv_App head (p, Q_Explicit))

    | Tm_Star l r ->
      let l = elab_term l in
      let r = elab_term r in
      mk_star l r
      
    | Tm_ExistsSL u b body
    | Tm_ForallSL u b body ->
      let t = elab_term b.binder_ty in
      let body = elab_term body in
      if Tm_ExistsSL? top
      then mk_exists u t (mk_abs_with_name b.binder_ppname.name t R.Q_Explicit body)
      else mk_forall u t (mk_abs_with_name b.binder_ppname.name t R.Q_Explicit body)

    | Tm_Inames ->
      pack_ln (Tv_FVar (pack_fv inames_lid))

    | Tm_EmpInames ->
      emp_inames_tm

    | Tm_Unknown ->
      pack_ln R.Tv_Unknown

    | Tm_FStar t _ ->
      t

let elab_st_comp (c:st_comp)
  : R.universe & R.term & R.term & R.term
  = let res = elab_term c.res in
    let pre = elab_term c.pre in
    let post = elab_term c.post in
    c.u, res, pre, post

let elab_comp (c:comp)
  : R.term
  = match c with
    | C_Tot t ->
      elab_term t

    | C_ST c ->
      let u, res, pre, post = elab_st_comp c in
      mk_stt_comp u res pre (mk_abs res R.Q_Explicit post)

    | C_STAtomic inames c ->
      let inames = elab_term inames in
      let u, res, pre, post = elab_st_comp c in
      mk_stt_atomic_comp u res inames pre (mk_abs res R.Q_Explicit post)

    | C_STGhost inames c ->
      let inames = elab_term inames in
      let u, res, pre, post = elab_st_comp c in
      mk_stt_ghost_comp u res inames pre (mk_abs res R.Q_Explicit post)

let elab_stt_equiv (g:R.env) (c:comp{C_ST? c}) (pre:R.term) (post:R.term)
  (eq_pre:RT.equiv g pre (elab_term (comp_pre c)))
  (eq_post:RT.equiv g post
                      (mk_abs (elab_term (comp_res c)) R.Q_Explicit (elab_term (comp_post c))))
  : RT.equiv g
      (let C_ST {u;res} = c in
       mk_stt_comp u
                   (elab_term res)
                   pre
                   post)
      (elab_comp c) =
  
  mk_stt_comp_equiv _
    (comp_u c)
    (elab_term (comp_res c))
    _ _ _ _ eq_pre eq_post

let elab_statomic_equiv (g:R.env) (c:comp{C_STAtomic? c}) (pre:R.term) (post:R.term)
  (eq_pre:RT.equiv g pre (elab_term (comp_pre c)))
  (eq_post:RT.equiv g post
                    (mk_abs (elab_term (comp_res c)) R.Q_Explicit (elab_term (comp_post c))))
  : RT.equiv g
      (let C_STAtomic inames {u;res} = c in
       mk_stt_atomic_comp u
                          (elab_term res)
                          (elab_term inames)
                          pre
                          post)
      (elab_comp c) =
  
  let C_STAtomic inames _ = c in
  mk_stt_atomic_comp_equiv _
    (comp_u c)
    (elab_term (comp_res c))
    (elab_term inames)
    _ _ _ _ eq_pre eq_post

let elab_stghost_equiv (g:R.env) (c:comp{C_STGhost? c}) (pre:R.term) (post:R.term)
  (eq_pre:RT.equiv g pre (elab_term (comp_pre c)))
  (eq_post:RT.equiv g post
                    (mk_abs (elab_term (comp_res c)) R.Q_Explicit (elab_term (comp_post c))))
  : RT.equiv g
      (let C_STGhost inames {u;res} = c in
       mk_stt_ghost_comp u
                         (elab_term res)
                         (elab_term inames)
                         pre
                         post)
      (elab_comp c) =
  
  let C_STGhost inames _ = c in
  mk_stt_ghost_comp_equiv _
    (comp_u c)
    (elab_term (comp_res c))
    (elab_term inames)
    _ _ _ _ eq_pre eq_post
