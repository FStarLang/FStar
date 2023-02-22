module Pulse.Elaborate.Pure
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax

let tun = R.pack_ln R.Tv_Unknown
let unit_lid = R.unit_lid
let bool_lid = R.bool_lid
let erased_lid = ["FStar"; "Ghost"; "erased"]
let hide_lid = ["FStar"; "Ghost"; "hide"]
let reveal_lid = ["FStar"; "Ghost"; "reveal"]
let vprop_lid = ["Steel"; "Effect"; "Common"; "vprop"]
let vprop_fv = R.pack_fv vprop_lid
let vprop_tm = R.pack_ln (R.Tv_FVar vprop_fv)
let unit_fv = R.pack_fv unit_lid
let unit_tm = R.pack_ln (R.Tv_FVar unit_fv)
let bool_fv = R.pack_fv bool_lid
let bool_tm = R.pack_ln (R.Tv_FVar bool_fv)

let true_tm = R.pack_ln (R.Tv_Const (R.C_True))
let false_tm = R.pack_ln (R.Tv_Const (R.C_False))

let emp_lid = ["Steel"; "Effect"; "Common"; "emp"]
let inames_lid = ["Steel"; "Memory"; "inames"]
let star_lid = ["Steel"; "Effect"; "Common"; "star"]
let pure_lid = ["Steel"; "ST"; "Util"; "pure"]
let exists_lid = ["Steel"; "ST"; "Util"; "exists_"]
let forall_lid = ["Steel"; "ST"; "Util"; "forall_"]
let args_of (tms:list R.term) =
  List.Tot.map (fun x -> x, R.Q_Explicit) tms

let uzero = R.pack_universe (R.Uv_Zero)

let steel_wrapper = ["Pulse"; "Steel"; "Wrapper"]
let mk_steel_wrapper_lid s = steel_wrapper@[s]

let emp_inames_lid = mk_steel_wrapper_lid "emp_inames"
let elim_pure_lid = mk_steel_wrapper_lid "elim_pure"

 //the thunked, value-type counterpart of the effect STT
let stt_lid = mk_steel_wrapper_lid "stt"
let stt_fv = R.pack_fv stt_lid
let stt_tm = R.pack_ln (R.Tv_FVar stt_fv)
let mk_stt_comp (u:R.universe) (res pre post:R.term) : Tot R.term =
  let t = R.pack_ln (R.Tv_UInst stt_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (res, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let stt_atomic_lid = mk_steel_wrapper_lid "stt_atomic"
let stt_atomic_fv = R.pack_fv stt_atomic_lid
let stt_atomic_tm = R.pack_ln (R.Tv_FVar stt_atomic_fv)
let mk_stt_atomic_comp (u:R.universe) (a inames pre post:R.term) =
  let t = R.pack_ln (R.Tv_UInst stt_atomic_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (inames, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let stt_ghost_lid = mk_steel_wrapper_lid "stt_ghost"
let stt_ghost_fv = R.pack_fv stt_ghost_lid
let stt_ghost_tm = R.pack_ln (R.Tv_FVar stt_ghost_fv)
let mk_stt_ghost_comp (u:R.universe) (a inames pre post:R.term) =
  let t = R.pack_ln (R.Tv_UInst stt_ghost_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (inames, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_total t = R.C_Total t
let binder_of_t_q t q = RT.mk_binder RT.pp_name_default 0 t q
let binder_of_t_q_s t q s = RT.mk_binder s 0 t q
let bound_var i : R.term = R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv i tun)))
let mk_name i : R.term = R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv i tun))) 

let arrow_dom = (R.term & R.aqualv)
let mk_arrow (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty q) (R.pack_comp (mk_total out)))
let mk_arrow_with_name (s:RT.pp_name_t) (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q_s ty q s) (R.pack_comp (mk_total out)))
let mk_abs ty qual t : R.term =  R.pack_ln (R.Tv_Abs (binder_of_t_q ty qual) t)
let mk_abs_with_name s ty qual t : R.term =  R.pack_ln (R.Tv_Abs (binder_of_t_q_s ty qual s) t)

let mk_erased (u:R.universe) (t:R.term) : R.term =
  let hd = R.pack_ln (R.Tv_UInst (R.pack_fv erased_lid) [u]) in
  R.pack_ln (R.Tv_App hd (t, R.Q_Explicit))

let mk_reveal (u:R.universe) (t:R.term) (e:R.term) : R.term =
  let hd = R.pack_ln (R.Tv_UInst (R.pack_fv reveal_lid) [u]) in
  let hd = R.pack_ln (R.Tv_App hd (t, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App hd (e, R.Q_Explicit))

let elim_exists_lid = mk_steel_wrapper_lid "elim_exists"
let intro_exists_lid = mk_steel_wrapper_lid "intro_exists"

let mk_exists (u:R.universe) (a p:R.term) =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv exists_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let mk_forall (u:R.universe) (a p:R.term) =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv forall_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let mk_elim_exists (u:R.universe) (a p:R.term) : R.term =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv elim_exists_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let mk_intro_exists (u:R.universe) (a p:R.term) (e:R.term) : R.term =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv intro_exists_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (p, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (e, R.Q_Explicit))

let while_lid = mk_steel_wrapper_lid "while_loop"

let mk_while (inv cond body:R.term) : R.term =
  let t = R.pack_ln (R.Tv_FVar (R.pack_fv while_lid)) in
  let t = R.pack_ln (R.Tv_App t (inv, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (cond, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (body, R.Q_Explicit))

let vprop_eq_tm t1 t2 =
  let open R in
  let u2 =
    pack_universe (Uv_Succ (pack_universe (Uv_Succ (pack_universe Uv_Zero)))) in
  let t = pack_ln (Tv_UInst (pack_fv eq2_qn) [u2]) in
  let t = pack_ln (Tv_App t (pack_ln (Tv_FVar (pack_fv vprop_lid)), Q_Implicit)) in
  let t = pack_ln (Tv_App t (t1, Q_Explicit)) in
  let t = pack_ln (Tv_App t (t2, Q_Explicit)) in
  t

let emp_inames_tm : R.term = R.pack_ln (R.Tv_FVar (R.pack_fv emp_inames_lid))

let non_informative_witness_lid = mk_steel_wrapper_lid "non_informative_witness"
let non_informative_witness_rt (u:R.universe) (a:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv non_informative_witness_lid) [u]) in
  let t = pack_ln (Tv_App t (a, Q_Explicit)) in
  t

let rec elab_universe (u:universe)
  : Tot R.universe
  = match u with
    | U_zero -> R.pack_universe (R.Uv_Zero)
    | U_succ u -> R.pack_universe (R.Uv_Succ (elab_universe u))
    | U_var x -> R.pack_universe (R.Uv_Name (x, Refl.Typing.Builtins.dummy_range))
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
      let! ty = elab_term b.binder_ty in
      let! phi = elab_term phi in
      Some (pack_ln (Tv_Refine (pack_bv (RT.make_bv_with_name b.binder_ppname 0 ty)) phi))

    | Tm_PureApp e1 q e2 ->
      let! e1 = elab_term e1 in
      let! e2 = elab_term e2 in
      Some (R.mk_app e1 [(e2, elab_qual q)])

    | Tm_Arrow b q c ->
      let! ty = elab_term b.binder_ty in
      let! c = elab_comp c in
      Some (mk_arrow_with_name b.binder_ppname (ty, elab_qual q) c)

    | Tm_Let t e1 e2 ->
      let! t = elab_term t in
      let! e1 = elab_term e1 in
      let! e2 = elab_term e2 in
      let bv = pack_bv (RT.make_bv 0 t) in
      Some (R.pack_ln (R.Tv_Let false [] bv e1 e2))

    | Tm_Type u ->
      Some (R.pack_ln (R.Tv_Type (elab_universe u)))
      
    | Tm_VProp ->
      Some (pack_ln (Tv_FVar (pack_fv vprop_lid)))

    | Tm_Emp ->
      Some (pack_ln (Tv_FVar (pack_fv emp_lid)))
      
    | Tm_Pure p ->
      let! p = elab_term p in
      let head = pack_ln (Tv_FVar (pack_fv pure_lid)) in
      Some (pack_ln (Tv_App head (p, Q_Explicit)))

    | Tm_Star l r ->
      let! l = elab_term l in
      let! r = elab_term r in      
      let head = pack_ln (Tv_FVar (pack_fv star_lid)) in      
      Some (R.mk_app head [(l, Q_Explicit); (r, Q_Explicit)])
      
    | Tm_ExistsSL u t body
    | Tm_ForallSL u t body ->
      let u = elab_universe u in
      let! t = elab_term t in
      let! b = elab_term body in
      if Tm_ExistsSL? top
      then Some (mk_exists u t (mk_abs t R.Q_Explicit b))
      else Some (mk_forall u t (mk_abs t R.Q_Explicit b))

    | Tm_Inames ->
      Some (pack_ln (Tv_FVar (pack_fv inames_lid)))

    | Tm_EmpInames -> Some emp_inames_tm

    | Tm_If _ _ _ _
    | Tm_Abs _ _ _ _ _
    | Tm_STApp _ _ _
    | Tm_Bind _ _
    | Tm_ElimExists _
    | Tm_IntroExists _ _
    | Tm_While _ _ _
    | Tm_UVar _ -> None
      //effectful constructs, explicitly not handled here
    
and elab_comp (c:comp) 
  : option R.term
  = match c with
    | C_Tot t ->
      elab_term t

    | C_ST c ->
      let! u, res, pre, post = elab_st_comp c in
      Some (mk_stt_comp u res pre (mk_abs res R.Q_Explicit post))

    | C_STAtomic inames c ->
      let! inames = elab_term inames in
      let! u, res, pre, post = elab_st_comp c in
      Some (mk_stt_atomic_comp u res inames pre
              (mk_abs res R.Q_Explicit post))

    | C_STGhost inames c ->
      let! inames = elab_term inames in
      let! u, res, pre, post = elab_st_comp c in
      Some (mk_stt_ghost_comp u res inames pre
              (mk_abs res R.Q_Explicit post))

and elab_st_comp (c:st_comp)
  : option (R.universe & R.term & R.term & R.term)
  = let! res = elab_term c.res in
    let! pre = elab_term c.pre in
    let! post = elab_term c.post in
    Some (elab_universe c.u, res, pre, post)
    
let is_pure_term (e:term) = Some? (elab_term e)
let pure_term = e:term { is_pure_term e }
let elab_pure (e:pure_term) : R.term = Some?.v (elab_term e)
let is_pure_comp (c:comp) = Some? (elab_comp c)
let is_pure_st_comp (c:st_comp) = Some? (elab_st_comp c)
let pure_comp = c:comp { is_pure_comp c }
let elab_pure_comp (c:pure_comp) = Some?.v (elab_comp c)
let pure_comp_st = c:pure_comp { stateful_comp c }
  
let ln_comp = c:pure_comp_st{ ln_c c }

#push-options "--z3rlimit_factor 4"
let rec opening_pure_term_with_pure_term (x:pure_term) (v:pure_term) (i:index)
  : Lemma (ensures is_pure_term (open_term' x v i))
          (decreases x)
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
              
    | Tm_ExistsSL _ t body
    | Tm_ForallSL _ t body ->
      aux t i; aux body (i + 1)
    
    | Tm_Arrow b _ c ->
      aux b.binder_ty i;
      opening_pure_comp_with_pure_term c v (i + 1)

and opening_pure_comp_with_pure_term (x:pure_comp) (v:pure_term) (i:index)
  : Lemma (ensures is_pure_comp (open_comp' x v i))
          (decreases x)
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
          (decreases x)
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
              
    | Tm_ExistsSL _ t body
    | Tm_ForallSL _ t body ->
      aux t i; aux body (i + 1)
    
    | Tm_Arrow b _ c ->
      aux b.binder_ty i;
      closing_pure_comp c v (i + 1)

and closing_pure_comp (x:pure_comp) (v:var) (i:index)
  : Lemma (ensures is_pure_comp (close_comp' x v i))
          (decreases x)
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


assume
val elab_freevars_inverse (e:pure_term)
  : Lemma 
    (ensures RT.freevars (elab_pure e) == freevars e)
