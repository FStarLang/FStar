module Pulse.Elaborate.Pure
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
assume
val dummy_range : Prims.range 
let tun = R.pack_ln R.Tv_Unknown
let bool_lid = ["Prims"; "bool"]
let vprop_lid = ["Steel"; "Effect"; "Common"; "vprop"]
let vprop_fv = R.pack_fv vprop_lid
let vprop_tm = R.pack_ln (R.Tv_FVar vprop_fv)
let emp_lid = ["Steel"; "Effect"; "Common"; "emp"]
let star_lid = ["Steel"; "Effect"; "Common"; "star"]
let pure_lid = ["Steel"; "ST"; "Util"; "pure"]
let exists_lid = ["Steel"; "ST"; "Util"; "exists_"]
let forall_lid = ["Steel"; "ST"; "Util"; "forall_"]
let stt_lid = ["Steel"; "ST"; "Util"; "stt"] //the thunked, value-type counterpart of the effect STT
let stt_fv = R.pack_fv stt_lid
let stt_tm = R.pack_ln (R.Tv_FVar stt_fv)
let mk_stt_app (u:R.universe) (args:list R.term) : R.term = 
  R.mk_app (R.pack_ln (R.Tv_UInst stt_fv [u])) (map (fun x -> x, R.Q_Explicit) args)
let mk_total t = R.C_Total t (R.pack_universe R.Uv_Unk) []
let binder_of_t_q t q = RT.mk_binder "_" 0 t q
let bound_var i : R.term = R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv i tun)))
let mk_name i : R.term = R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv i tun))) 
let arrow_dom = (R.term & R.aqualv)
let mk_tot_arrow1 (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty q) (R.pack_comp (mk_total out)))


let mk_abs ty t =  R.pack_ln (R.Tv_Abs (binder_of_t_q ty R.Q_Explicit) t)

let rec elab_universe (u:universe)
  : Tot R.universe
  = match u with
    | U_zero -> R.pack_universe (R.Uv_Zero)
    | U_succ u -> R.pack_universe (R.Uv_Succ (elab_universe u))
    | U_var x -> R.pack_universe (R.Uv_Name (x, dummy_range))
    | U_max u1 u2 -> R.pack_universe (R.Uv_Max [elab_universe u1; elab_universe u2])

let mk_st (u:universe) (res pre post:R.term)
  : Tot R.term 
  = mk_stt_app (elab_universe u) [res; pre; mk_abs res post]

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


let rec elab_term (top:term)
  : option R.term
  = let open R in
    match top with
    | Tm_BVar n -> 
      let bv = pack_bv (RT.make_bv n tun) in
      Some (pack_ln (Tv_BVar bv))
      
    | Tm_Var n ->
      // tun because type does not matter at a use site
      let bv = pack_bv (RT.make_bv n tun) in
      Some (pack_ln (Tv_Var bv))

    | Tm_FVar l ->
      Some (pack_ln (Tv_FVar (pack_fv l)))

    | Tm_Constant c ->
      Some (pack_ln (Tv_Const (elab_const c)))
    
    | Tm_PureApp e1 e2 ->
      let? e1 = elab_term e1 in
      let? e2 = elab_term e2 in
      Some (R.mk_app e1 [(e2, Q_Explicit)])

    | Tm_Arrow t c ->
      let? t = elab_term t in
      let? c = elab_comp c in
      Some (mk_tot_arrow1 (t, R.Q_Explicit) c)

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

    | Tm_If b then_ else_ ->
      let? b = elab_term b in
      let? then_ = elab_term then_ in
      let? else_ = elab_term else_ in
      let then_branch = R.Pat_Constant R.C_True, then_ in
      let else_branch = R.Pat_Constant R.C_False, else_ in
      Some (R.pack_ln (Tv_Match b None [then_branch; else_branch]))

    | Tm_Abs _ _ _
    | Tm_STApp _ _
    | Tm_Bind _ _ _ -> None
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

let is_pure_term (e:term) = Some? (elab_term e)
let pure_term = e:term { is_pure_term e }
let elab_pure (e:pure_term) : R.term = Some?.v (elab_term e)
let is_pure_comp (c:comp) = Some? (elab_comp c)
let pure_comp = c:comp { is_pure_comp c }
let elab_pure_comp (c:pure_comp) = Some?.v (elab_comp c)
let pure_comp_st = c:pure_comp { C_ST? c }

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
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Emp -> ()

    // | Tm_Abs t pre_hint body ->
    //   aux t i;
    //   aux body (i + 1)

    | Tm_PureApp l r
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
    
    | Tm_Arrow t c ->
      aux t i;
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
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Emp -> ()

    // | Tm_Abs t pre_hint body ->
    //   aux t i;
    //   aux body (i + 1)

    | Tm_PureApp l r
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
    
    | Tm_Arrow t c ->
      aux t i;
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
