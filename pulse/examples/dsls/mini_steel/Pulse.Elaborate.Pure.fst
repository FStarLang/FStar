module Pulse.Elaborate.Pure
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax

let tun = R.pack_ln R.Tv_Unknown
let bool_lid = ["Prims"; "bool"]
let vprop_lid = ["Steel"; "Effect"; "Common"; "vprop"]
let vprop_fv = R.pack_fv vprop_lid
let vprop_tm = R.pack_ln (R.Tv_FVar vprop_fv)
let emp_lid = ["Steel"; "Effect"; "Common"; "emp"]
let inames_lid = ["Steel"; "Memory"; "inames"]
let star_lid = ["Steel"; "Effect"; "Common"; "star"]
let pure_lid = ["Steel"; "ST"; "Util"; "pure"]
let exists_lid = ["Steel"; "ST"; "Util"; "exists_"]
let forall_lid = ["Steel"; "ST"; "Util"; "forall_"]
let args_of (tms:list R.term) =
  List.Tot.map (fun x -> x, R.Q_Explicit) tms

let steel_wrapper = ["Pulse"; "Steel"; "Wrapper"]
let mk_steel_wrapper_lid s = steel_wrapper@[s]

 //the thunked, value-type counterpart of the effect STT
let stt_lid = mk_steel_wrapper_lid "stt"
let stt_fv = R.pack_fv stt_lid
let stt_tm = R.pack_ln (R.Tv_FVar stt_fv)
let mk_stt_app (u:R.universe) (args:list R.term) : Tot R.term = 
  R.mk_app (R.pack_ln (R.Tv_UInst stt_fv [u])) (args_of args)

let stt_atomic_lid = mk_steel_wrapper_lid "stt_atomic"
let stt_atomic_fv = R.pack_fv stt_atomic_lid
let stt_atomic_tm = R.pack_ln (R.Tv_FVar stt_atomic_fv)
let mk_stt_atomic_app (u:R.universe) (args:list R.term)
  : Tot R.term = 
  R.mk_app (R.pack_ln (R.Tv_UInst stt_atomic_fv [u])) (args_of args)

let stt_ghost_lid = mk_steel_wrapper_lid "stt_ghost"
let stt_ghost_fv = R.pack_fv stt_ghost_lid
let stt_ghost_tm = R.pack_ln (R.Tv_FVar stt_ghost_fv)
let mk_stt_ghost_app (u:R.universe) (args:list R.term)
  : Tot R.term = 
  R.mk_app (R.pack_ln (R.Tv_UInst stt_ghost_fv [u])) (args_of args)

let mk_total t = R.C_Total t
let binder_of_t_q t q = RT.mk_binder "_" 0 t q
let binder_of_t_q_s t q s = RT.mk_binder s 0 t q
let bound_var i : R.term = R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv i tun)))
let mk_name i : R.term = R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv i tun))) 
let arrow_dom = (R.term & R.aqualv)
let mk_tot_arrow1 (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty q) (R.pack_comp (mk_total out)))
let mk_tot_arrow_with_name1 (s:string) (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q_s ty q s) (R.pack_comp (mk_total out)))

let vprop_eq_tm t1 t2 =
  let open R in
  let u2 =
    pack_universe (Uv_Succ (pack_universe (Uv_Succ (pack_universe Uv_Zero)))) in
  let t = pack_ln (Tv_UInst (pack_fv eq2_qn) [u2]) in
  let t = pack_ln (Tv_App t (pack_ln (Tv_FVar (pack_fv vprop_lid)), Q_Implicit)) in
  let t = pack_ln (Tv_App t (t1, Q_Explicit)) in
  let t = pack_ln (Tv_App t (t2, Q_Explicit)) in
  t

let emp_inames_tm : R.term =
  `(FStar.Ghost.hide #(Steel.Memory.inames) (FStar.Set.empty #Steel.Memory.iname))

let mk_abs ty qual t : R.term =  R.pack_ln (R.Tv_Abs (binder_of_t_q ty qual) t)

let mk_abs_with_name s ty qual t : R.term =  R.pack_ln (R.Tv_Abs (binder_of_t_q_s ty qual s) t)

let rec elab_universe (u:universe)
  : Tot R.universe
  = match u with
    | U_zero -> R.pack_universe (R.Uv_Zero)
    | U_succ u -> R.pack_universe (R.Uv_Succ (elab_universe u))
    | U_var x -> R.pack_universe (R.Uv_Name (x, Refl.Typing.Builtins.dummy_range))
    | U_max u1 u2 -> R.pack_universe (R.Uv_Max [elab_universe u1; elab_universe u2])

let mk_st (u:universe) (res pre post:R.term)
  : Tot R.term =
  mk_stt_app (elab_universe u) [res; pre; mk_abs res R.Q_Explicit post]

let mk_st_atomic (u:universe) (res inames pre post:R.term)
  : Tot R.term =
  mk_stt_atomic_app (elab_universe u) [res; inames; pre; mk_abs res R.Q_Explicit post]

let mk_st_ghost (u:universe) (res inames pre post:R.term)
  : Tot R.term =
  mk_stt_ghost_app (elab_universe u) [res; inames; pre; mk_abs res R.Q_Explicit post]

let (let?) (f:option 'a) (g: 'a -> option 'b) : option 'b = 
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
  : option R.term
  = let open R in
    match top with
    | Tm_BVar bv ->
      let bv = pack_bv (RT.make_bv_with_name bv.bv_ppname bv.bv_index tun) in
      Some (pack_ln (Tv_BVar bv))
      
    | Tm_Var nm ->
      // tun because type does not matter at a use site
      let bv = pack_bv (RT.make_bv_with_name nm.nm_ppname nm.nm_index tun) in
      Some (pack_ln (Tv_Var bv))

    | Tm_FVar l ->
      Some (pack_ln (Tv_FVar (pack_fv l)))

    | Tm_UInst l us ->
      Some (pack_ln (Tv_UInst (pack_fv l) (List.Tot.map elab_universe us)))

    | Tm_Constant c ->
      Some (pack_ln (Tv_Const (elab_const c)))

    | Tm_Refine b phi ->
      let? ty = elab_term b.binder_ty in
      let? phi = elab_term phi in
      Some (pack_ln (Tv_Refine (pack_bv (RT.make_bv_with_name b.binder_ppname 0 ty)) phi))

    | Tm_PureApp e1 q e2 ->
      let? e1 = elab_term e1 in
      let? e2 = elab_term e2 in
      Some (R.mk_app e1 [(e2, elab_qual q)])

    | Tm_Arrow b q c ->
      let? ty = elab_term b.binder_ty in
      let? c = elab_comp c in
      Some (mk_tot_arrow_with_name1 b.binder_ppname (ty, elab_qual q) c)

    | Tm_Let t e1 e2 ->
      let? t = elab_term t in
      let? e1 = elab_term e1 in
      let? e2 = elab_term e2 in
      let bv = pack_bv (RT.make_bv 0 t) in
      Some (R.pack_ln (R.Tv_Let false [] bv e1 e2))

    | Tm_Type u ->
      Some (R.pack_ln (R.Tv_Type (elab_universe u)))
      
    | Tm_VProp ->
      Some (pack_ln (Tv_FVar (pack_fv vprop_lid)))

    | Tm_Emp ->
      Some (pack_ln (Tv_FVar (pack_fv emp_lid)))
      
    | Tm_Pure p ->
      let? p = elab_term p in
      let head = pack_ln (Tv_FVar (pack_fv pure_lid)) in
      Some (pack_ln (Tv_App head (p, Q_Explicit)))

    | Tm_Star l r ->
      let? l = elab_term l in
      let? r = elab_term r in      
      let head = pack_ln (Tv_FVar (pack_fv star_lid)) in      
      Some (R.mk_app head [(l, Q_Explicit); (r, Q_Explicit)])
      
    | Tm_ExistsSL t body
    | Tm_ForallSL t body ->    
      let? t = elab_term t in
      let? b = elab_term body in
      let body = R.pack_ln (R.Tv_Abs (binder_of_t_q t R.Q_Explicit) b) in
      let head = 
        let head_lid = 
          if Tm_ExistsSL? top
          then exists_lid
          else forall_lid 
        in
        pack_ln (Tv_FVar (pack_fv head_lid)) in
      Some (R.mk_app head ([(t, Q_Implicit); (body, Q_Explicit)]))

    | Tm_If b then_ else_ -> (* this should be stateful *)
      let? b = elab_term b in
      let? then_ = elab_term then_ in
      let? else_ = elab_term else_ in
      let then_branch = R.Pat_Constant R.C_True, then_ in
      let else_branch = R.Pat_Constant R.C_False, else_ in
      Some (R.pack_ln (Tv_Match b None [then_branch; else_branch]))

    | Tm_Inames ->
      Some (pack_ln (Tv_FVar (pack_fv inames_lid)))

    | Tm_EmpInames -> Some emp_inames_tm

    | Tm_Abs _ _ _ _ _
    | Tm_STApp _ _ _
    | Tm_Bind _ _
    | Tm_UVar _ -> None
      //effectful constructs, explicitly not handled here
    
and elab_comp (c:comp) 
  : option R.term
  = match c with
    | C_Tot t ->
      elab_term t

    | C_ST c ->
      let? res = elab_term c.res in
      let? pre = elab_term c.pre in
      let? post = elab_term c.post in
      Some (mk_st c.u res pre post)

    | C_STAtomic inames c ->
      let? inames = elab_term inames in
      let? res = elab_term c.res in
      let? pre = elab_term c.pre in
      let? post = elab_term c.post in
      Some (mk_st_atomic c.u res inames pre post)

    | C_STGhost inames c ->
      let? inames = elab_term inames in
      let? res = elab_term c.res in
      let? pre = elab_term c.pre in
      let? post = elab_term c.post in
      Some (mk_st_ghost c.u res inames pre post)

let is_pure_term (e:term) = Some? (elab_term e)
let pure_term = e:term { is_pure_term e }
let elab_pure (e:pure_term) : R.term = Some?.v (elab_term e)
let is_pure_comp (c:comp) = Some? (elab_comp c)
let pure_comp = c:comp { is_pure_comp c }
let elab_pure_comp (c:pure_comp) = Some?.v (elab_comp c)
let pure_comp_st = c:pure_comp { stateful_comp c }
  
let ln_comp = c:pure_comp_st{ ln_c c }

#push-options "--z3rlimit_factor 2"
let rec opening_pure_term_with_pure_term (x:pure_term) (v:pure_term) (i:index)
  : Lemma (ensures is_pure_term (open_term' x v i))
          [SMTPat (is_pure_term (open_term' x v i))]
  = let aux (y:pure_term {y << x}) (j:index)
      : Lemma (ensures (is_pure_term (open_term' y v j)))
      = opening_pure_term_with_pure_term y v j
    in
    match x with
    | Tm_BVar _
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Emp -> ()

    // | Tm_Abs t pre_hint body ->
    //   aux t i;
    //   aux body (i + 1)

    | Tm_Refine b phi ->
      aux b.binder_ty i;
      aux phi (i + 1)        

    | Tm_PureApp l _ r
    // | Tm_STApp l r
    | Tm_Star l r ->    
      aux l i; aux r i
                 
    | Tm_Let t e1 e2  ->
    // | Tm_Bind t e1 e2 ->    
      aux t i; aux e1 i; aux e2 (i + 1)
      
    | Tm_Pure p ->
      aux p i
              
    | Tm_ExistsSL t body
    | Tm_ForallSL t body ->
      aux t i; aux body (i + 1)
    
    | Tm_Arrow b _ c ->
      aux b.binder_ty i;
      opening_pure_comp_with_pure_term c v (i + 1)

    | Tm_If b then_ else_ ->
      aux b i; aux then_ i; aux else_ i

and opening_pure_comp_with_pure_term (x:pure_comp) (v:pure_term) (i:index)
  : Lemma (ensures is_pure_comp (open_comp' x v i))
          [SMTPat (is_pure_comp (open_comp' x v i))]
  = match x with
    | C_Tot t ->
      opening_pure_term_with_pure_term t v i
      
    | C_ST { res; pre; post } ->
      opening_pure_term_with_pure_term res v i;
      opening_pure_term_with_pure_term pre v i;
      opening_pure_term_with_pure_term post v (i + 1)

    | C_STAtomic inames { res; pre; post }
    | C_STGhost inames { res; pre; post } ->
      opening_pure_term_with_pure_term inames v i;
      opening_pure_term_with_pure_term res v i;
      opening_pure_term_with_pure_term pre v i;
      opening_pure_term_with_pure_term post v (i + 1)

let rec closing_pure_term (x:pure_term) (v:var) (i:index)
  : Lemma (ensures is_pure_term (close_term' x v i))
          [SMTPat (is_pure_term (close_term' x v i))]
  = let aux (y:pure_term {y << x}) (j:index)
      : Lemma (ensures (is_pure_term (close_term' y v j)))
      = closing_pure_term y v j
    in
    match x with
    | Tm_BVar _
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Emp -> ()

    // | Tm_Abs t pre_hint body ->
    //   aux t i;
    //   aux body (i + 1)

    | Tm_Refine b phi ->
      aux b.binder_ty i;
      aux phi (i + 1)

    | Tm_PureApp l _ r
    // | Tm_STApp l r
    | Tm_Star l r ->    
      aux l i; aux r i
                 
    | Tm_Let t e1 e2  ->
    // | Tm_Bind t e1 e2 ->    
      aux t i; aux e1 i; aux e2 (i + 1)
      
    | Tm_Pure p ->
      aux p i
              
    | Tm_ExistsSL t body
    | Tm_ForallSL t body ->
      aux t i; aux body (i + 1)
    
    | Tm_Arrow b _ c ->
      aux b.binder_ty i;
      closing_pure_comp c v (i + 1)

    | Tm_If b then_ else_ ->
      aux b i; aux then_ i; aux else_ i

and closing_pure_comp (x:pure_comp) (v:var) (i:index)
  : Lemma (ensures is_pure_comp (close_comp' x v i))
          [SMTPat (is_pure_comp (close_comp' x v i))]
  = match x with
    | C_Tot t ->
      closing_pure_term t v i
      
    | C_ST { res; pre; post } -> 
      closing_pure_term res v i;
      closing_pure_term pre v i;
      closing_pure_term post v (i + 1)

    | C_STAtomic inames { res; pre; post }
    | C_STGhost inames { res; pre; post } ->
      closing_pure_term inames v i;
      closing_pure_term res v i;
      closing_pure_term pre v i;
      closing_pure_term post v (i + 1)
#pop-options
