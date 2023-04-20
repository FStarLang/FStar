module Pulse.Elaborate.Pure
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax

open Pulse.Reflection.Util

let rec elab_universe (u:universe)
  : Tot R.universe
  = match u with
    | U_unknown -> R.pack_universe (R.Uv_Unk)
    | U_zero -> R.pack_universe (R.Uv_Zero)
    | U_succ u -> R.pack_universe (R.Uv_Succ (elab_universe u))
    | U_var x -> R.pack_universe (R.Uv_Name (x, FStar.Reflection.Typing.Builtins.dummy_range))
    | U_max u1 u2 -> R.pack_universe (R.Uv_Max [elab_universe u1; elab_universe u2])

let (let!) (f:option 'a) (g: 'a -> option 'b) : option 'b = 
  match f with
  | None -> None
  | Some x -> g x
let elab_const (c:constant)
  : R.vconst
  = match c with
    | Unit -> R.C_Unit
    | Bool true -> R.C_True
    | Bool false -> R.C_False
    | Int i -> R.C_Int i

let elab_qual = function
  | None -> R.Q_Explicit
  | Some Implicit -> R.Q_Implicit
  
let rec elab_term (top:term)
  : R.term
  = let open R in
    match top with
    | Tm_BVar bv ->
      let bv = pack_bv (RT.make_bv_with_name bv.bv_ppname bv.bv_index tun) in
      pack_ln (Tv_BVar bv)
      
    | Tm_Var nm ->
      // tun because type does not matter at a use site
      let bv = pack_bv (RT.make_bv_with_name nm.nm_ppname nm.nm_index tun) in
      pack_ln (Tv_Var bv)

    | Tm_FVar l ->
      pack_ln (Tv_FVar (pack_fv l.fv_name))

    | Tm_UInst l us ->
      pack_ln (Tv_UInst (pack_fv l.fv_name) (List.Tot.map elab_universe us))

    | Tm_Constant c ->
      pack_ln (Tv_Const (elab_const c))

    | Tm_Refine b phi ->
      let ty = elab_term b.binder_ty in
      let phi = elab_term phi in
      pack_ln (Tv_Refine (pack_bv (RT.make_bv_with_name b.binder_ppname 0 ty)) phi)

    | Tm_PureApp e1 q e2 ->
      let e1 = elab_term e1 in
      let e2 = elab_term e2 in
      R.mk_app e1 [(e2, elab_qual q)]

    | Tm_Arrow b q c ->
      let ty = elab_term b.binder_ty in
      let c = elab_comp c in
      mk_arrow_with_name b.binder_ppname (ty, elab_qual q) c

    | Tm_Let t e1 e2 ->
      let t = elab_term t in
      let e1 = elab_term e1 in
      let e2 = elab_term e2 in
      let bv = pack_bv (RT.make_bv 0 t) in
      R.pack_ln (R.Tv_Let false [] bv e1 e2)

    | Tm_Type u ->
      R.pack_ln (R.Tv_Type (elab_universe u))
      
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
      let u = elab_universe u in
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
    
and elab_comp (c:comp) 
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

and elab_st_comp (c:st_comp)
  : R.universe & R.term & R.term & R.term
  = let res = elab_term c.res in
    let pre = elab_term c.pre in
    let post = elab_term c.post in
    elab_universe c.u, res, pre, post

let elab_stt_equiv (g:R.env) (c:comp{C_ST? c}) (pre:R.term) (post:R.term)
  (eq_pre:RT.equiv g pre (elab_term (comp_pre c)))
  (eq_post:RT.equiv g post
                      (mk_abs (elab_term (comp_res c)) R.Q_Explicit (elab_term (comp_post c))))
  : RT.equiv g
      (let C_ST {u;res} = c in
       mk_stt_comp (elab_universe u)
                   (elab_term res)
                   pre
                   post)
      (elab_comp c) =
  
  mk_stt_comp_equiv _
    (elab_universe (comp_u c))
    (elab_term (comp_res c))
    _ _ _ _ eq_pre eq_post

let elab_statomic_equiv (g:R.env) (c:comp{C_STAtomic? c}) (pre:R.term) (post:R.term)
  (eq_pre:RT.equiv g pre (elab_term (comp_pre c)))
  (eq_post:RT.equiv g post
                    (mk_abs (elab_term (comp_res c)) R.Q_Explicit (elab_term (comp_post c))))
  : RT.equiv g
      (let C_STAtomic inames {u;res} = c in
       mk_stt_atomic_comp (elab_universe u)
                          (elab_term res)
                          (elab_term inames)
                          pre
                          post)
      (elab_comp c) =
  
  let C_STAtomic inames _ = c in
  mk_stt_atomic_comp_equiv _
    (elab_universe (comp_u c))
    (elab_term (comp_res c))
    (elab_term inames)
    _ _ _ _ eq_pre eq_post

let elab_stghost_equiv (g:R.env) (c:comp{C_STGhost? c}) (pre:R.term) (post:R.term)
  (eq_pre:RT.equiv g pre (elab_term (comp_pre c)))
  (eq_post:RT.equiv g post
                    (mk_abs (elab_term (comp_res c)) R.Q_Explicit (elab_term (comp_post c))))
  : RT.equiv g
      (let C_STGhost inames {u;res} = c in
       mk_stt_ghost_comp (elab_universe u)
                          (elab_term res)
                          (elab_term inames)
                          pre
                          post)
      (elab_comp c) =
  
  let C_STGhost inames _ = c in
  mk_stt_ghost_comp_equiv _
    (elab_universe (comp_u c))
    (elab_term (comp_res c))
    (elab_term inames)
    _ _ _ _ eq_pre eq_post
