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
    | Tm_PureApp e1 q e2 ->
      let e1 = elab_term e1 in
      let e2 = elab_term e2 in
      R.mk_app e1 [(e2, elab_qual q)]

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
      
    | Tm_ExistsSL u t body _
    | Tm_ForallSL u t body ->
      let t = elab_term t in
      let b = elab_term body in
      if Tm_ExistsSL? top
      then mk_exists u t (mk_abs t R.Q_Explicit b)
      else mk_forall u t (mk_abs t R.Q_Explicit b)

    | Tm_Inames ->
      pack_ln (Tv_FVar (pack_fv inames_lid))

    | Tm_EmpInames ->
      emp_inames_tm

    | Tm_UVar _
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

let tm_bvar (bv:bv) : term =
  Tm_FStar (R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv_with_name bv.bv_ppname bv.bv_index))))
           bv.bv_range

let tm_var (nm:nm) : term =
  Tm_FStar (R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv_with_name nm.nm_ppname nm.nm_index))))
           nm.nm_range

let tm_fvar (l:fv) : term =
  Tm_FStar (R.pack_ln (R.Tv_FVar (R.pack_fv l.fv_name)))
           l.fv_range

// let is_tm_fvar (t:term) : option fv =
//   match t with
//   | Tm_FStar host_term fv_range ->
//     (match R.inspect_ln host_term with
//      | R.Tv_FVar fv -> Some {fv_name=R.inspect_fv fv; fv_range}
//      | _ -> None)
//   | _ -> None

let tm_uinst (l:fv) (us:list universe) : term =
  Tm_FStar (R.pack_ln (R.Tv_UInst (R.pack_fv l.fv_name) us))
           l.fv_range

// let is_tm_uinst (t:term) : option (fv & list universe) =
//   match t with
//   | Tm_FStar host_term fv_range ->
//     (match R.inspect_ln host_term with
//      | R.Tv_UInst fv us -> Some ({fv_name=R.inspect_fv fv; fv_range}, us)
//      | _ -> None)
//   | _ -> None
  
let tm_constant (c:constant) : term =
  Tm_FStar (R.pack_ln (R.Tv_Const c)) FStar.Range.range_0

let tm_refine (b:binder) (t:term) : term =
  Tm_FStar (R.pack_ln (R.Tv_Refine (R.pack_bv (RT.make_bv_with_name b.binder_ppname 0))
                                   (elab_term b.binder_ty)
                                   (elab_term t)))
           FStar.Range.range_0

let tm_let (t e1 e2:term) : term =
  Tm_FStar (R.pack_ln (R.Tv_Let false
                                []
                                (R.pack_bv (RT.make_bv 0))
                                (elab_term t)
                                (elab_term e1)
                                (elab_term e2)))
           FStar.Range.range_0

let tm_arrow (b:binder) (q:option qualifier) (c:comp) : term =
  Tm_FStar (mk_arrow_with_name b.binder_ppname (elab_term b.binder_ty, elab_qual q)
                                               (elab_comp c))
           FStar.Range.range_0

let tm_type (u:universe) : term =
  Tm_FStar (R.pack_ln (R.Tv_Type u)) FStar.Range.range_0

let mk_bvar (s:string) (r:Range.range) (i:index) : term =
  tm_bvar {bv_index=i;bv_ppname=RT.seal_pp_name s;bv_range=r}

let null_var (v:var) : term =
  tm_var {nm_index=v;nm_ppname=RT.pp_name_default;nm_range=Range.range_0}

let null_bvar (i:index) : term =
  tm_bvar {bv_index=i;bv_ppname=RT.pp_name_default;bv_range=Range.range_0}

let term_of_nvar (x:nvar) : term =
  tm_var { nm_ppname=fst x; nm_index=snd x; nm_range=FStar.Range.range_0}
let term_of_no_name_var (x:var) : term =
  term_of_nvar (v_as_nv x)
