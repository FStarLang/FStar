module MiniSteel
module RT = Refl.Typing
module R = FStar.Reflection
open FStar.List.Tot
  
type lident = R.name

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

let return_lid = ["Steel"; "ST"; "Util"; "return_stt"]
let return_noeq_lid = ["Steel"; "ST"; "Util"; "return_stt_noeq"]
let bind_lid = ["Steel"; "ST"; "Util"; "bind_stt"]
let bind_fv = R.pack_fv bind_lid
let bind_univ_inst u1 u2 = R.pack_ln (R.Tv_UInst bind_fv [u1;u2])
let mk_total t = R.C_Total t (R.pack_universe R.Uv_Unk) []
let binder_of_t_q t q = RT.mk_binder "_" 0 t q
let bound_var i : R.term = R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv i (R.pack_ln R.Tv_Unknown))))
let mk_name i : R.term = R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv i (R.pack_ln R.Tv_Unknown)))) 
let arrow_dom = (R.term & R.aqualv)
let mk_tot_arrow1 (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty q) (R.pack_comp (mk_total out)))
let rec mk_tot_arrow (formals:list (R.term & R.aqualv)) (res:R.term) : R.term =
  match formals with
  | [] -> res
  | hd :: tl -> 
    let out = mk_tot_arrow tl res in
    mk_tot_arrow1 hd out

let bind_res (u2:R.universe) (t2 pre post2:R.term) =
  mk_stt_app u2 [t2; pre; post2]

let g_type_bind (u2:R.universe) (t1 t2 post1 post2:R.term) =
    mk_tot_arrow1 (t1, R.Q_Explicit)
                  (bind_res u2 t2 (R.mk_app post1 [bound_var 0 (* x *), R.Q_Explicit]) post2)

let bind_type_t1_t2_pre_post1_post2_f (u1 u2:R.universe) (t1 t2 pre post1 post2:R.term) =
  mk_tot_arrow1 (g_type_bind u2 t1 t2 post1 post2, R.Q_Explicit)
                (bind_res u2 t2 pre post2)

let bind_type_t1_t2_pre_post1_post2 (u1 u2:R.universe) (t1 t2 pre post1 post2:R.term) =
  let f_type = mk_stt_app u1 [t1; pre; post1] in
  mk_tot_arrow1 (f_type, R.Q_Explicit)
                (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2)

let post2_type_bind t2 = mk_tot_arrow1 (t2, R.Q_Explicit) vprop_tm
let bind_type_t1_t2_pre_post1 (u1 u2:R.universe) (t1 t2 pre post1:R.term) =
  let var = 0 in
  let post2 = mk_name var in
  mk_tot_arrow1 (post2_type_bind t2, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2) (RT.CloseVar var) 0)

let post1_type_bind t1 = mk_tot_arrow [(t1, R.Q_Explicit)] vprop_tm
let bind_type_t1_t2_pre (u1 u2:R.universe) (t1 t2 pre:R.term) =
  let var = 1 in
  let post1 = mk_name var in
  mk_tot_arrow1 (post1_type_bind t1, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1) (RT.CloseVar var) 0)

let bind_type_t1_t2 (u1 u2:R.universe) (t1 t2:R.term) =
  let var = 2 in
  let pre = mk_name var in
  let pre_type = vprop_tm in
  mk_tot_arrow1 (pre_type, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1_t2_pre u1 u2 t1 t2 pre) (RT.CloseVar var) 0)

let bind_type_t1 (u1 u2:R.universe) (t1:R.term) =
  let var = 3 in
  let t2 = mk_name var in
  let t2_type = RT.tm_type u2 in
  mk_tot_arrow1 (t2_type, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1_t2 u1 u2 t1 t2) (RT.CloseVar var) 0)

let bind_type (u1 u2:R.universe) =
  let var = 4 in
  let t1 = mk_name var in
  let t1_type = RT.tm_type u1 in
  mk_tot_arrow1 (t1_type, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1 u1 u2 t1) (RT.CloseVar var) 0)

#push-options "--fuel 2 --ifuel 1 --query_stats"
let inst_bind_t1 #u1 #u2 #g #head
                   (head_typing: RT.typing g head (bind_type u1 u2))
                   (#t1:_)
                   (t1_typing: RT.typing g t1 (RT.tm_type u1))
  : GTot (RT.typing g (R.mk_app head [(t1, R.Q_Implicit)]) (bind_type_t1 u1 u2 t1))
  = let open_with_spec (t v:R.term)
      : Lemma (RT.open_with t v == RT.open_or_close_term' t (RT.OpenWith v) 0)
              [SMTPat (RT.open_with t v)]
      = RT.open_with_spec t v
    in
    let d : RT.typing g (R.mk_app head [(t1, R.Q_Implicit)]) _ =
      RT.T_App _ _ _ _ _ _ head_typing t1_typing
    in
    assume (bind_type_t1 u1 u2 t1 ==
            RT.open_with (RT.open_or_close_term' (bind_type_t1 u1 u2 (mk_name 4))
                                                 (RT.CloseVar 4) 0)
                         t1);

    d
#pop-options    



let inst_bind_t2 #u1 #u2 #g #head #t1
                   (head_typing: RT.typing g head (bind_type_t1 u1 u2 t1))
                   (#t2:_)
                   (t2_typing: RT.typing g t2 (RT.tm_type u2))
  : RT.typing g (R.mk_app head [(t2, R.Q_Implicit)]) (bind_type_t1_t2 u1 u2 t1 t2)
  = admit()


let inst_bind_pre #u1 #u2 #g #head #t1 #t2
                  (head_typing: RT.typing g head (bind_type_t1_t2 u1 u2 t1 t2))
                  (#pre:_)
                  (pre_typing: RT.typing g pre vprop_tm)
  : RT.typing g (R.mk_app head [(pre, R.Q_Implicit)]) (bind_type_t1_t2_pre u1 u2 t1 t2 pre)
  = admit()

let inst_bind_post1 #u1 #u2 #g #head #t1 #t2 #pre
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre u1 u2 t1 t2 pre))
                  (#post1:_)
                  (post1_typing: RT.typing g post1 (post1_type_bind t1))
  : RT.typing g (R.mk_app head [(post1, R.Q_Implicit)]) (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1)
  = admit()

let inst_bind_post2 #u1 #u2 #g #head #t1 #t2 #pre #post1
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1))
                  (#post2:_)
                  (post2_typing: RT.typing g post2 (post2_type_bind t2))
  : RT.typing g (R.mk_app head [(post2, R.Q_Implicit)]) (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2)
  = admit()

let inst_bind_f #u1 #u2 #g #head #t1 #t2 #pre #post1 #post2
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2))
                  (#f:_)
                  (f_typing: RT.typing g f (mk_stt_app u1 [t1; pre; post1]))
  : RT.typing g (R.mk_app head [(f, R.Q_Explicit)]) (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2)
  = admit()

let inst_bind_g #u1 #u2 #g #head #t1 #t2 #pre #post1 #post2
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2))
                  (#gg:_)
                  (g_typing: RT.typing g gg (g_type_bind u2 t1 t2 post1 post2))
  : RT.typing g (R.mk_app head [(gg, R.Q_Explicit)]) (bind_res u2 t2 pre post2)
  = let open_with_spec (t v:R.term)
      : Lemma (RT.open_with t v == RT.open_or_close_term' t (RT.OpenWith v) 0)
              [SMTPat (RT.open_with t v)]
      = RT.open_with_spec t v
    in
    let d : RT.typing g (R.mk_app head [(gg, R.Q_Explicit)]) _ =
      RT.T_App _ _ _ _ _ _ head_typing g_typing
    in
    admit();
    d


let frame_lid = ["Steel"; "ST"; "Util"; "frame_stt"]
let subsumption_lid = ["Steel"; "ST"; "Util"; "sub_stt"]

type constant =
  | Unit
  | Bool of bool
  | Int of int

let as_vconst (c:constant) 
  : R.vconst
  = match c with
    | Unit -> R.C_Unit
    | Bool true -> R.C_True
    | Bool false -> R.C_False
    | Int i -> R.C_Int i

let var = nat
let index = nat  

type universe = 
  | U_zero
  | U_succ of universe
  | U_var of string
  | U_max : universe -> universe -> universe
  
type term =
  | Tm_BVar     : i:index -> term
  | Tm_Var      : v:var -> term
  | Tm_FVar     : l:lident -> term
  | Tm_Constant : c:constant -> term
  | Tm_Abs      : t:term -> pre_hint:vprop -> body:term -> term
  | Tm_PureApp  : head:term -> arg:term -> term
  | Tm_Let      : t:term -> e1:term -> e2:term -> term  
  | Tm_STApp    : head:term -> arg:term -> term  
  | Tm_Bind     : t:term -> e1:term -> e2:term -> term
  | Tm_Emp      : term
  | Tm_Pure     : p:term -> term
  | Tm_Star     : l:vprop -> r:vprop -> term
  | Tm_ExistsSL : t:term -> body:vprop -> term
  | Tm_ForallSL : t:term -> body:vprop -> term
  | Tm_Arrow    : t:term -> body:comp -> term 
  | Tm_Type     : universe -> term
  | Tm_VProp    : term
  | Tm_If       : b:term -> then_:term -> else_:term -> term

and comp = 
  | C_Tot : term -> comp
  | C_ST  : st_comp -> comp

and st_comp = {
  u:universe;
  res:term;
  pre:vprop;
  post:vprop
}

and vprop = term

let rec open_term' (t:term) (v:term) (i:index)
  : Tot term (decreases t)
  = match t with
    | Tm_BVar j -> if i = j then v else t

    | Tm_Var _
    | Tm_FVar _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Emp -> t

    | Tm_Abs t pre_hint body ->
      Tm_Abs (open_term' t v i)
             (open_term' pre_hint v i)
             (open_term' body v (i + 1))

    | Tm_PureApp head arg ->
      Tm_PureApp (open_term' head v i)
                 (open_term' arg v i)
                 
    | Tm_Let t e1 e2 ->
      Tm_Let (open_term' t v i)
             (open_term' e1 v i)
             (open_term' e2 v (i + 1))
             
    | Tm_STApp head arg ->
      Tm_STApp (open_term' head v i)
               (open_term' arg v i)

    | Tm_Bind t e1 e2 ->
      Tm_Bind (open_term' t v i)
              (open_term' e1 v i)
              (open_term' e2 v (i + 1))

    | Tm_Pure p ->
      Tm_Pure (open_term' p v i)
      
    | Tm_Star l r ->
      Tm_Star (open_term' l v i)
              (open_term' r v i)
              
    | Tm_ExistsSL t body ->
      Tm_ExistsSL (open_term' t v i)
                  (open_term' body v (i + 1))
                  
    | Tm_ForallSL t body ->
      Tm_ForallSL (open_term' t v i)
                  (open_term' body v (i + 1))
    
    | Tm_Arrow t c ->
      Tm_Arrow (open_term' t v i)
               (open_comp' c v (i + 1))

    | Tm_If b then_ else_ ->
      Tm_If (open_term' b v i)
            (open_term' then_ v i)
            (open_term' else_ v i)

and open_comp' (c:comp) (v:term) (i:index)
  : Tot comp (decreases c)
  = match c with
    | C_Tot t ->
      C_Tot (open_term' t v i)

    | C_ST c ->
      C_ST { c with res = open_term' c.res v i;
                    pre = open_term' c.pre v i;
                    post = open_term' c.post v (i + 1) }
    
let open_term t v = open_term' t (Tm_Var v) 0
let open_comp_with (c:comp) (x:term) = open_comp' c x 0

let rec close_term' (t:term) (v:var) (i:index)
  : term
  = match t with
    | Tm_Var m -> if m = v then Tm_BVar i else t
    
    | Tm_BVar _
    | Tm_FVar _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Emp -> t

    | Tm_Abs t pre_hint body ->
      Tm_Abs (close_term' t v i)
             (close_term' pre_hint v i)
             (close_term' body v (i + 1))

    | Tm_PureApp head arg ->
      Tm_PureApp (close_term' head v i)
                 (close_term' arg v i)
                 
    | Tm_Let t e1 e2 ->
      Tm_Let (close_term' t v i)
             (close_term' e1 v i)
             (close_term' e2 v (i + 1))
             
    | Tm_STApp head arg ->
      Tm_STApp (close_term' head v i)
               (close_term' arg v i)

    | Tm_Bind t e1 e2 ->
      Tm_Bind (close_term' t v i)
              (close_term' e1 v i)
              (close_term' e2 v (i + 1))

    | Tm_Pure p ->
      Tm_Pure (close_term' p v i)
      
    | Tm_Star l r ->
      Tm_Star (close_term' l v i)
              (close_term' r v i)
              
    | Tm_ExistsSL t body ->
      Tm_ExistsSL (close_term' t v i)
                  (close_term' body v (i + 1))
                  
    | Tm_ForallSL t body ->
      Tm_ForallSL (close_term' t v i)
                  (close_term' body v (i + 1))
    
    | Tm_Arrow t c ->
      Tm_Arrow (close_term' t v i)
               (close_comp' c v (i + 1))

    | Tm_If b then_ else_ ->
      Tm_If (close_term' b v i)
            (close_term' then_ v i)
            (close_term' else_ v i)

and close_comp' (c:comp) (v:var) (i:index)
  : Tot comp (decreases c)
  = match c with
    | C_Tot t ->
      C_Tot (close_term' t v i)

    | C_ST c ->
      C_ST { c with res = close_term' c.res v i;
                    pre = close_term' c.pre v i;
                    post = close_term' c.post v (i + 1) }

let close_term t v = close_term' t v 0
let close_comp t v = close_comp' t v 0

assume
val dummy_range : Prims.range 
let rec elab_universe (u:universe)
  : Tot R.universe
  = match u with
    | U_zero -> R.pack_universe (R.Uv_Zero)
    | U_succ u -> R.pack_universe (R.Uv_Succ (elab_universe u))
    | U_var x -> R.pack_universe (R.Uv_Name (x, dummy_range))
    | U_max u1 u2 -> R.pack_universe (R.Uv_Max [elab_universe u1; elab_universe u2])

let fstar_env =
  g:R.env { 
    RT.lookup_fvar g RT.bool_fv == Some (RT.tm_type RT.u_zero) /\
    RT.lookup_fvar g vprop_fv == Some (RT.tm_type (elab_universe (U_succ (U_succ U_zero)))) /\
    (forall (u1 u2:R.universe). RT.lookup_fvar_uinst g bind_fv [u1; u2] == Some (bind_type u1 u2))
    ///\ star etc
  }

let fstar_top_env =
  g:fstar_env { 
    forall x. None? (RT.lookup_bvar g x )
  }

let tun = R.pack_ln R.Tv_Unknown

let (let?) (f:option 'a) (g: 'a -> option 'b) : option 'b = 
  match f with
  | None -> None
  | Some x -> g x

let mk_abs ty t =  R.pack_ln (R.Tv_Abs (binder_of_t_q ty R.Q_Explicit) t)

let mk_st (u:universe) (res pre post:R.term)
  : Tot R.term 
  = mk_stt_app (elab_universe u) [res; pre; mk_abs res post]
  
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
      Some (pack_ln (Tv_Const (as_vconst c)))
    
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
let typ = term //pure_term
let is_pure_comp (c:comp) = Some? (elab_comp c)
let pure_comp = c:comp { is_pure_comp c }
let pure_comp_st = c:pure_comp { C_ST? c }
let comp_pre (c:pure_comp_st)
  : pure_term 
  = let C_ST s = c in s.pre

let eqn = pure_term & pure_term & pure_term
let binding = either pure_term eqn
let env = list (var & binding)


let mk_bind (u1 u2:universe)
            (ty1 ty2:R.term)
            (pre1 post1: R.term)
            (post2: R.term)
            (t1 t2:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid)
                         [elab_universe u1; elab_universe u2]) in
    R.mk_app
      (R.mk_app
        (R.mk_app
          (R.mk_app 
            (R.mk_app 
              (R.mk_app 
                (R.mk_app head
                          [(ty1, R.Q_Implicit)])
                [(ty2, R.Q_Implicit)])
              [(pre1, R.Q_Implicit)])
            [(post1, R.Q_Implicit)])
          [(post2, R.Q_Implicit)])
        [(t1, R.Q_Explicit)])
      [(t2, R.Q_Explicit)]

let elab_bind (c1 c2:pure_comp_st) (e1 e2:R.term) =
  let C_ST c1 = c1 in
  let C_ST c2 = c2 in
  let ty1 = elab_pure c1.res in
  let ty2 = elab_pure c2.res in
  mk_bind c1.u c2.u
          ty1 ty2
          (elab_pure c1.pre)
          (mk_abs ty1 (elab_pure c1.post))
          (mk_abs ty2 (elab_pure c2.post))
          e1 e2

let elab_pure_comp (c:pure_comp) = Some?.v (elab_comp c)


let elab_eqn (e:eqn)
  : R.term
  = let ty, l, r = e in
    let ty = elab_pure ty in
    let l = elab_pure l in
    let r = elab_pure r in
    RT.eq2 ty l r

let elab_binding (b:binding)
  : R.term 
  = match b with
    | Inl t -> elab_pure t
    | Inr eqn -> elab_eqn eqn

module L = FStar.List.Tot
let extend_env_l (f:R.env) (g:env) : R.env = 
  L.fold_right 
    (fun (x, b) g ->  
      let t = elab_binding b in
      RT.extend_env g x t)
     g
     f


let comp_post (c:pure_comp_st) = let C_ST s = c in s.post

let comp_res (c:comp) : term =
  match c with
  | C_Tot ty -> ty
  | C_ST c -> c.res

let comp_u (c:pure_comp_st) = let C_ST s = c in s.u


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

let rec lookup (e:list (var & 'a)) (x:var)
  : option 'a
  = match e with
    | [] -> None
    | (y, v) :: tl -> if x = y then Some v else lookup tl x

let lookup_ty (e:env) (x:var)
  : option typ
  = match lookup e x with
    | Some (Inl t) -> Some t
    | _ -> None

assume
val freevars (t:term) : FStar.Set.set var

let freevars_comp (c:comp) : FStar.Set.set var =
  match c with
  | C_Tot t -> freevars t
  | C_ST st -> freevars st.res `Set.union` freevars st.pre `Set.union` freevars st.post

let tm_bool : pure_term = Tm_FVar bool_lid

let tm_true : pure_term = Tm_Constant (Bool true)

let tm_false : pure_term = Tm_Constant (Bool false)

let mk_eq2 (t:pure_term) (e0 e1:pure_term) 
  : pure_term
  = Tm_PureApp
         (Tm_PureApp (Tm_PureApp (Tm_FVar R.eq2_qn) t)
                      e0) e1

let return_comp (u:universe) (t:pure_term) (e:pure_term)
  : pure_comp 
  = C_ST { u;
           res = t;
           pre = Tm_Emp;
           post = Tm_Pure (mk_eq2 t (Tm_BVar 0) e) }

let return_comp_noeq (u:universe) (t:pure_term)
  : pure_comp 
  = C_ST { u;
           res = t;
           pre = Tm_Emp;
           post = Tm_Emp }

[@@erasable]
noeq
type vprop_equiv (f:fstar_top_env) : env -> pure_term -> pure_term -> Type =
  | VE_Refl:
     g:env ->
     t:pure_term ->
     vprop_equiv f g t t

  | VE_Sym:
     g:env ->
     t1:pure_term -> 
     t2:pure_term -> 
     vprop_equiv f g t1 t2 ->
     vprop_equiv f g t2 t1

  | VE_Trans:
     g:env ->
     t0:pure_term ->
     t1:pure_term ->
     t2:pure_term ->
     vprop_equiv f g t0 t1 ->
     vprop_equiv f g t1 t2 ->
     vprop_equiv f g t0 t2

  | VE_Ctxt:
     g:env ->
     t0:pure_term -> 
     t1:pure_term -> 
     t0':pure_term -> 
     t1':pure_term ->
     vprop_equiv f g t0 t0' ->
     vprop_equiv f g t1 t1' ->
     vprop_equiv f g (Tm_Star t0 t1) (Tm_Star t0' t1')
     
  | VE_Unit:
     g:env ->
     t:pure_term ->
     vprop_equiv f g (Tm_Star Tm_Emp t) t

  | VE_Comm:
     g:env ->
     t0:pure_term ->
     t1:pure_term ->
     vprop_equiv f g (Tm_Star t0 t1) (Tm_Star t1 t0)
     
  | VE_Assoc:
     g:env ->
     t0:pure_term ->
     t1:pure_term ->
     t2:pure_term ->
     vprop_equiv f g (Tm_Star t0 (Tm_Star t1 t2)) (Tm_Star (Tm_Star t0 t1) t2)

  // | VE_Ex:
  //    g:env ->
  //    x:var { None? (lookup_ty g x) } ->
  //    ty:pure_term ->
  //    t0:pure_term ->
  //    t1:pure_term ->
  //    vprop_equiv f ((x, Inl ty)::g) (open_term t0 x) (open_term t1 x) ->
  //    vprop_equiv f g (Tm_ExistsSL ty t0) (Tm_ExistsSL ty t1)

  // | VE_Fa:
  //    g:env ->
  //    x:var { None? (lookup_ty g x) } ->
  //    ty:pure_term ->
  //    t0:pure_term ->
  //    t1:pure_term ->
  //    vprop_equiv f ((x, Inl ty)::g) (open_term t0 x) (open_term t1 x) ->
  //    vprop_equiv f g (Tm_ForallSL ty t0) (Tm_ForallSL ty t1)

[@@erasable]
noeq
type st_equiv (f:fstar_top_env) : env -> pure_comp -> pure_comp -> Type =
  | ST_VPropEquiv :
      g:env ->
      c1:pure_comp_st ->
      c2:pure_comp_st { comp_res c1 == comp_res c2 } -> 
      x:var { None? (lookup_ty g x) } ->
      vprop_equiv f g (comp_pre c1) (comp_pre c2) ->
      vprop_equiv f ((x, Inl (comp_res c1))::g) (open_term (comp_post c1) x) (open_term (comp_post c2) x) ->      
      st_equiv f g c1 c2

  | ST_ElabEquiv:
      g:env ->
      c1:pure_comp_st ->
      c2:pure_comp_st ->
      RT.equiv (extend_env_l f g) (elab_pure_comp c1) (elab_pure_comp c2) ->
      st_equiv f g c1 c2


let add_frame (s:pure_comp_st) (frame:pure_term)
  : pure_comp_st
  = let C_ST s = s in
    C_ST { s with pre = Tm_Star s.pre frame;
                  post = Tm_Star s.post frame }

let close_pure_comp (c:pure_comp) (x:var) : pure_comp = close_comp c x

[@@erasable]
noeq
type my_erased (a:Type) = | E of a

noeq
type src_typing (f:fstar_top_env) : env -> term -> pure_comp -> Type =
  | T_Tot: 
      g:env ->
      e:pure_term ->
      ty:pure_term ->
      RT.typing (extend_env_l f g) (elab_pure e) (elab_pure ty) ->
      src_typing f g e (C_Tot ty)

  | T_Abs: 
      g:env ->
      x:var { None? (lookup g x) } ->
      ty:pure_term ->
      u:universe ->
      body:term ->
      c:pure_comp ->
      hint:vprop ->
      tot_typing f g ty (Tm_Type u) ->
      src_typing f ((x, Inl ty)::g) (open_term body x) c ->
      src_typing f g (Tm_Abs ty hint body) (C_Tot (Tm_Arrow ty (close_pure_comp c x)))
  
  | T_STApp :
      g:env ->
      head:term -> 
      formal:pure_term ->
      res:pure_comp {C_ST? res} ->
      arg:pure_term ->
      src_typing f g head (C_Tot (Tm_Arrow formal res)) ->
      tot_typing f g arg formal ->
      src_typing f g (Tm_STApp head arg) (open_comp_with res arg)

  | T_Return:
      g:env ->
      e:pure_term -> 
      t:pure_term -> 
      u:universe ->
      tot_typing f g e t ->
      universe_of f g t u ->
      src_typing f g e (return_comp u t e)

  | T_ReturnNoEq:
      g:env ->
      e:term -> 
      t:pure_term -> 
      u:universe ->
      src_typing f g e (C_Tot t) ->
      universe_of f g t u ->
      src_typing f g e (return_comp_noeq u t)

  | T_Bind:
      g:env ->
      e1:term ->
      e2:term ->
      c1:pure_comp_st ->
      c2:pure_comp_st ->
      x:var { None? (lookup g x) (*  /\ ~(x `Set.mem` freevars e2) *) } ->
      c:pure_comp ->
      src_typing f g e1 c1 ->
      tot_typing f g (comp_res c1) (Tm_Type (comp_u c1)) -> //type-correctness; would be nice to derive it instead      
      src_typing f ((x, Inl (comp_res c1))::g) (open_term e2 x) c2 ->
      bind_comp f g x c1 c2 c ->
      src_typing f g (Tm_Bind (comp_res c1) e1 e2) c

  | T_If:
      g:env ->
      b:pure_term -> 
      e1:term ->
      e2:term -> 
      c:pure_comp ->
      hyp:var { None? (lookup g hyp) // /\ ~ (hyp `Set.mem` freevars e1) /\ ~ (hyp `Set.mem` freevars e2)
  } ->
      tot_typing f g b tm_bool ->
      src_typing f ((hyp, Inr (tm_bool, b, tm_true)) :: g) e1 c ->
      src_typing f ((hyp, Inr (tm_bool, b, tm_false)) :: g) e2 c ->
      src_typing f g (Tm_If b e1 e2) c

  | T_Frame:
      g:env ->
      e:term ->
      c:pure_comp_st ->
      frame:pure_term ->
      tot_typing f g frame Tm_VProp ->
      src_typing f g e c ->
      src_typing f g e (add_frame c frame)

  | T_Equiv:
      g:env ->
      e:term ->
      c:pure_comp ->
      c':pure_comp ->      
      src_typing f g e c ->
      st_equiv f g c c' ->
      src_typing f g e c' 

and tot_typing (f:fstar_top_env) (g:env) (e:term) (t:pure_term) =
  my_erased (src_typing f g e (C_Tot t))

and universe_of (f:fstar_top_env) (g:env) (t:term) (u:universe) =
  tot_typing f g t (Tm_Type u)

and bind_comp (f:fstar_top_env) : env -> var -> pure_comp -> pure_comp -> pure_comp -> Type =
  | Bind_comp :
      g:env ->
      x:var { None? (lookup g x) } ->
      c1:pure_comp_st ->
      c2:pure_comp_st {  open_term (comp_post c1) x == comp_pre c2 /\ ~ (x `Set.mem` freevars (comp_post c2)) } ->
      //x doesn't escape in the result type
      universe_of f g (comp_res c2) (comp_u c2) ->
      //or in the result post; free var check isn't enough; we need typability
      y:var { None? (lookup g y) } ->      
      tot_typing f ((y, Inl (comp_res c2)) :: g) (open_term (comp_post c2) y) Tm_VProp ->
      bind_comp f g x c1 c2 (C_ST {u = comp_u c2; res = comp_res c2; pre = comp_pre c1; post=comp_post c2})


let star_typing_inversion (f:_) (g:_) (t0 t1:term) (d:tot_typing f g (Tm_Star t0 t1) Tm_VProp)
  : (tot_typing f g t0 Tm_VProp &
     tot_typing f g t1 Tm_VProp)
  = admit()

let star_typing (#f:_) (#g:_) (#t0 #t1:term)
                (d0:tot_typing f g t0 Tm_VProp)
                (d1:tot_typing f g t1 Tm_VProp)
  : tot_typing f g (Tm_Star t0 t1) Tm_VProp
  = admit()

let emp_typing (#f:_) (#g:_) 
  : tot_typing f g Tm_Emp Tm_VProp
  = admit()

let rec vprop_equiv_typing (f:_) (g:_) (t0 t1:pure_term) (v:vprop_equiv f g t0 t1)
  : GTot ((tot_typing f g t0 Tm_VProp -> tot_typing f g t1 Tm_VProp) &
          (tot_typing f g t1 Tm_VProp -> tot_typing f g t0 Tm_VProp))
        (decreases v)
  = match v with
    | VE_Refl _ _ -> (fun x -> x), (fun x -> x)

    | VE_Sym _ _ _ v' -> 
      let f, g = vprop_equiv_typing f g t1 t0 v' in
      g, f

    | VE_Trans g t0 t2 t1 v02 v21 ->
      let f02, f20 = vprop_equiv_typing _ _ _ _ v02 in
      let f21, f12 = vprop_equiv_typing _ _ _ _ v21 in
      (fun x -> f21 (f02 x)), 
      (fun x -> f20 (f12 x))

    | VE_Ctxt g s0 s1 s0' s1' v0 v1 ->
      let f0, f0' = vprop_equiv_typing _ _ _ _ v0 in
      let f1, f1' = vprop_equiv_typing _ _ _ _ v1 in      
      let ff (x:tot_typing f g (Tm_Star s0 s1) Tm_VProp)
        : tot_typing f g (Tm_Star s0' s1') Tm_VProp
        = let s0_typing, s1_typing = star_typing_inversion _ _ _ _ x in
          let s0'_typing, s1'_typing = f0 s0_typing, f1 s1_typing in
          star_typing s0'_typing s1'_typing
      in
      let gg (x:tot_typing f g (Tm_Star s0' s1') Tm_VProp)
        : tot_typing f g (Tm_Star s0 s1) Tm_VProp
        = let s0'_typing, s1'_typing = star_typing_inversion _ _ _ _ x in
          star_typing (f0' s0'_typing) (f1' s1'_typing)        
      in
      ff, gg

    | VE_Unit g t ->
      let fwd (x:tot_typing f g (Tm_Star Tm_Emp t) Tm_VProp)
        : tot_typing f g t Tm_VProp
        = let _, r = star_typing_inversion _ _ _ _ x in
          r
      in
      let bk (x:tot_typing f g t Tm_VProp)
        : tot_typing f g (Tm_Star Tm_Emp t) Tm_VProp
        = star_typing emp_typing x
      in
      fwd, bk

    | VE_Comm g t0 t1 ->
      let f t0 t1 (x:tot_typing f g (Tm_Star t0 t1) Tm_VProp)
        : tot_typing f g (Tm_Star t1 t0) Tm_VProp
        = let tt0, tt1 = star_typing_inversion _ _ _ _ x in
          star_typing tt1 tt0
      in
      f t0 t1, f t1 t0

    | VE_Assoc g t0 t1 t2 ->
      let fwd (x:tot_typing f g (Tm_Star t0 (Tm_Star t1 t2)) Tm_VProp)
        : tot_typing f g (Tm_Star (Tm_Star t0 t1) t2) Tm_VProp
        = let tt0, tt12 = star_typing_inversion _ _ _ _ x in
          let tt1, tt2 = star_typing_inversion _ _ _ _ tt12 in
          star_typing (star_typing tt0 tt1) tt2
      in
      let bk (x : tot_typing f g (Tm_Star (Tm_Star t0 t1) t2) Tm_VProp)
        : tot_typing f g (Tm_Star t0 (Tm_Star t1 t2)) Tm_VProp
        = let tt01, tt2 = star_typing_inversion _ _ _ _ x in
          let tt0, tt1 = star_typing_inversion _ _ _ _ tt01 in
          star_typing tt0 (star_typing tt1 tt2)
      in
      fwd, bk

    // | VE_Ex g x ty t0 t1 _
    // | VE_Fa g x ty t0 t1 _ ->
    //   //these require inversion of typing on abstractions
    //   admit()

  
module L = FStar.List.Tot
let max (n1 n2:nat) = if n1 < n2 then n2 else n1

let rec fresh (e:list (var & 'a))
  : var
  = match e with
    | [] -> 0
    | (y, _) :: tl ->  max (fresh tl) y + 1
    | _ :: tl -> fresh tl

let rec fresh_not_mem (e:list (var & 'a)) (elt: (var & 'a))
  : Lemma (ensures L.memP elt e ==> fresh e > fst elt)
  = match e with
    | [] -> ()
    | hd :: tl -> fresh_not_mem tl elt
  
let rec lookup_mem (e:list (var & 'a)) (x:var)
  : Lemma
    (requires Some? (lookup e x))
    (ensures exists elt. L.memP elt e /\ fst elt == x)
  = match e with
    | [] -> ()
    | hd :: tl -> 
      match lookup tl x with
      | None -> assert (L.memP hd e)
      | _ -> 
        lookup_mem tl x;
        eliminate exists elt. L.memP elt tl /\ fst elt == x
        returns _
        with _ . ( 
          introduce exists elt. L.memP elt e /\ fst elt == x
          with elt
          and ()
        )

let fresh_is_fresh (e:env)
  : Lemma (None? (lookup e (fresh e)))
          [SMTPat (lookup e (fresh e))]
  =  match lookup e (fresh e) with
     | None -> ()
     | Some _ ->
       lookup_mem e (fresh e);
       FStar.Classical.forall_intro (fresh_not_mem e)
module RT = Refl.Typing

module T = FStar.Tactics      

assume
val tc_meta_callback (f:R.env) (e:R.term) 
  : T.Tac (option (t:R.term & RT.typing f e t))

assume
val readback_ty (t:R.term)
  : T.Tac (option (ty:typ { elab_term ty == Some t }))

let check_universe (f:fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(u:universe & universe_of f g t u) { is_pure_term t })
  = let f = extend_env_l f g in
    match elab_term t with
    | None -> T.fail "Not a syntactically pure term"
    | Some rt ->
      match tc_meta_callback f rt with
      | None -> T.fail "Not typeable"
      | Some (| ty', tok |) ->
        match readback_ty ty' with
        | Some (Tm_Type u) -> (| u, E (T_Tot _ _ _ tok) |)
        | _ -> T.fail "Not typeable as a universe"
      
let check_tot_univ (f:fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(u:universe &
              ty:pure_term &
              universe_of f g ty u &
              src_typing f g t (C_Tot ty)) { is_pure_term t } )
  = let fg = extend_env_l f g in
    match elab_term t with
    | None -> T.fail "Not a syntactically pure term"
    | Some rt -> 
      match tc_meta_callback fg rt with
      | None -> T.fail "Not typeable"
      | Some (| ty', tok |) ->
        match readback_ty ty' with
        | None -> T.fail "Inexpressible type"
        | Some ty -> 
          let (| u, uty |) = check_universe f g ty in
          (| u, ty, uty, T_Tot g t ty tok |)

let check_tot (f:fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(ty:pure_term &
              src_typing f g t (C_Tot ty)) { is_pure_term t })
  = let fg = extend_env_l f g in
    match elab_term t with
    | None -> T.fail "Not a syntactically pure term"
    | Some rt -> 
      match tc_meta_callback fg rt with
      | None -> T.fail "Not typeable"
      | Some (| ty', tok |) ->
        match readback_ty ty' with
        | None -> T.fail "Inexpressible type"
        | Some ty -> 
          (| ty, T_Tot g t ty tok |)

let rec vprop_as_list (vp:pure_term)
  : list pure_term
  = match vp with
    | Tm_Star vp0 vp1 -> vprop_as_list vp0 @ vprop_as_list vp1
    | _ -> [vp]

let rec list_as_vprop (vps:list pure_term)
  : pure_term
  = match vps with
    | [] -> Tm_Emp
    | hd::tl -> Tm_Star hd (list_as_vprop tl)

let canon_vprop (vp:pure_term)
  : pure_term
  = list_as_vprop (vprop_as_list vp)

let rec list_as_vprop_append f g (vp0 vp1:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                          (Tm_Star (list_as_vprop vp0) 
                                   (list_as_vprop vp1)))
         (decreases vp0)
  = match vp0 with
    | [] -> 
      let v : vprop_equiv f g (list_as_vprop vp1)
                              (Tm_Star Tm_Emp (list_as_vprop vp1)) = VE_Sym _ _ _ (VE_Unit _ _)
      in
      v
    | hd::tl ->
      let tl_vp1 = list_as_vprop_append f g tl vp1 in
      let d : vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star hd (Tm_Star (list_as_vprop tl) (list_as_vprop vp1)))
            = VE_Ctxt _ _ _ _ _ (VE_Refl _ _) tl_vp1
      in
      let d : vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star (Tm_Star hd (list_as_vprop tl)) (list_as_vprop vp1))
            = VE_Trans _ _ _ _ d (VE_Assoc _ _ _ _) in
      d

let list_as_vprop_comm f g (vp0 vp1:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                          (list_as_vprop (vp1 @ vp0)))
  = let d1 : _ = list_as_vprop_append f g vp0 vp1 in
    let d2 : _ = VE_Sym _ _ _ (list_as_vprop_append f g vp1 vp0) in
    let d1 : _ = VE_Trans _ _ _ _ d1 (VE_Comm _ _ _) in
    VE_Trans _ _ _ _ d1 d2

let list_as_vprop_assoc f g (vp0 vp1 vp2:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ (vp1 @ vp2)))
                          (list_as_vprop ((vp0 @ vp1) @ vp2)))
  = List.Tot.append_assoc vp0 vp1 vp2;
    VE_Refl _ _
  
let rec vprop_list_equiv (f:fstar_top_env)
                         (g:env)
                         (vp:pure_term)
  : GTot (vprop_equiv f g vp (canon_vprop vp))
         (decreases vp)
  = match vp with
    | Tm_Star vp0 vp1 ->
      let eq0 = vprop_list_equiv f g vp0 in
      let eq1 = vprop_list_equiv f g vp1 in      
      let app_eq
        : vprop_equiv _ _ (canon_vprop vp) (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = list_as_vprop_append f g (vprop_as_list vp0) (vprop_as_list vp1)
      in
      let step
        : vprop_equiv _ _ vp (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = VE_Ctxt _ _ _ _ _ eq0 eq1
      in
      VE_Trans _ _ _ _ step (VE_Sym _ _ _ app_eq)
      
    | _ -> 
      VE_Sym _ _ _
        (VE_Trans _ _ _ _ (VE_Comm g vp Tm_Emp) (VE_Unit _ vp))

module L = FStar.List.Tot.Base
let rec maybe_split_one_vprop (p:term) (qs:list pure_term)
  : option (list pure_term & list pure_term)
  = match qs with
    | [] -> None
    | q::qs -> 
      if p = q
      then Some ([], qs)
      else match maybe_split_one_vprop p qs with
           | None -> None
           | Some (l, r) -> Some (q::l, r)
    
let can_split_one_vprop p qs = Some? (maybe_split_one_vprop p qs)

let split_one_vprop_l (p:pure_term) 
                      (qs:list pure_term { can_split_one_vprop p qs })
  : list pure_term
  = let Some (l, r) = maybe_split_one_vprop p qs in
    l

let split_one_vprop_r (p:pure_term) 
                      (qs:list pure_term { can_split_one_vprop p qs })
  : list pure_term
  = let Some (l, r) = maybe_split_one_vprop p qs in
    r

let vprop_equiv_swap (f:_) (g:_) (l0 l1 l2:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop ((l0 @ l1) @ l2))
                          (list_as_vprop (l1 @ (l0 @ l2))))
  = let d1 : _ = list_as_vprop_append f g (l0 @ l1) l2 in
    let d2 = VE_Trans _ _ _ _ d1 (VE_Ctxt _ _ _ _ _ (list_as_vprop_comm _ _ _ _) (VE_Refl _ _)) in
    let d3 = VE_Sym _ _ _ (list_as_vprop_append f g (l1 @ l0) l2) in
    let d4 = VE_Trans _ _ _ _ d2 d3 in
    List.Tot.append_assoc l1 l0 l2;
    d4

let split_one_vprop (p:pure_term) 
                    (qs:list pure_term { can_split_one_vprop p qs })
  : list pure_term
  = split_one_vprop_l p qs @ split_one_vprop_r p qs 

let split_one_vprop_equiv f g (p:pure_term) (qs:list pure_term { can_split_one_vprop p qs })
  : vprop_equiv f g (list_as_vprop qs) (Tm_Star p (list_as_vprop (split_one_vprop p qs)))
  = let rec aux (qs:list pure_term { can_split_one_vprop p qs })
      : Lemma (qs == ((split_one_vprop_l p qs @ [p]) @ split_one_vprop_r p qs))
      = match qs with
        | q :: qs ->
          if p = q then ()
          else aux qs
    in
    aux qs;
    vprop_equiv_swap f g (split_one_vprop_l p qs) [p] (split_one_vprop_r p qs)

let rec try_split_vprop f g (req:list pure_term) (ctxt:list pure_term)
  : option (frame:list pure_term &
            vprop_equiv f g (list_as_vprop (req @ frame)) (list_as_vprop ctxt))
  = match req with
    | [] -> Some (| ctxt, VE_Refl g _ |)
    | hd::tl ->
      match maybe_split_one_vprop hd ctxt with
      | None -> None
      | Some (l, r) -> 
        let d1 : vprop_equiv f g (list_as_vprop ctxt) (list_as_vprop (hd :: (l@r))) = split_one_vprop_equiv _ _ hd ctxt in
        match try_split_vprop f g tl (l @ r) with
        | None -> None
        | Some (| frame, d |) ->
          let d : vprop_equiv f g (list_as_vprop (tl @ frame)) (list_as_vprop (l @ r)) = d in
          let dd : vprop_equiv f g (list_as_vprop (req @ frame)) (list_as_vprop (hd :: (l @ r))) = 
              VE_Ctxt _ _ _ _ _ (VE_Refl _ hd) d
          in
          let ddd = VE_Trans _ _ _ _ dd (VE_Sym _ _ _ d1) in
          Some (| frame, ddd |)
                       
let split_vprop (f:fstar_top_env)
                (g:env)
                (ctxt:pure_term)
                (ctxt_typing: tot_typing f g ctxt Tm_VProp)
                (req:pure_term)
   : T.Tac (frame:pure_term &
            tot_typing f g frame Tm_VProp &
            vprop_equiv f g (Tm_Star req frame) ctxt)
   = let ctxt_l = vprop_as_list ctxt in
     let req_l = vprop_as_list req in
     match try_split_vprop f g req_l ctxt_l with
     | None -> T.fail "Could not find frame"
     | Some (| frame, veq |) ->
       let d1 
         : vprop_equiv _ _ (Tm_Star (canon_vprop req) (list_as_vprop frame))
                           (list_as_vprop (req_l @ frame))
         = VE_Sym _ _ _ (list_as_vprop_append f g req_l frame)
       in
       let d1 
         : vprop_equiv _ _ (Tm_Star req (list_as_vprop frame))
                           (list_as_vprop (req_l @ frame))
         = VE_Trans _ _ _ _ (VE_Ctxt _ _ _ _ _ (vprop_list_equiv f g req) (VE_Refl _ _)) d1
       in
       let d : vprop_equiv _ _ (Tm_Star req (list_as_vprop frame))
                               (canon_vprop ctxt) =
           VE_Trans _ _ _ _ d1 veq
       in
       let d : vprop_equiv _ _ (Tm_Star req (list_as_vprop frame))
                               ctxt =
         VE_Trans _ _ _ _ d (VE_Sym _ _ _ (vprop_list_equiv f g ctxt))
       in
       let typing : tot_typing f g (list_as_vprop frame) Tm_VProp = 
         let fwd, bk = vprop_equiv_typing _ _ _ _ d in
         let star_typing = bk ctxt_typing in
         snd (star_typing_inversion _ _ _ _ star_typing)
       in
       (| list_as_vprop frame, typing, d |)

#push-options "--query_stats --fuel 1 --ifuel 2 --z3rlimit_factor 4"
let try_frame_pre (#f:fstar_top_env)
                  (#g:env)
                  (#t:term)
                  (#pre:pure_term)
                  (pre_typing: tot_typing f g pre Tm_VProp)
                  (#c:pure_comp { C_ST? c })
                  (t_typing: src_typing f g t c)
  : T.Tac (c':pure_comp_st { comp_pre c' == pre } &
           src_typing f g t c')
  = let C_ST s = c in
    let (| frame, frame_typing, ve |) = split_vprop f g pre pre_typing s.pre in
    let t_typing
      : src_typing f g t (add_frame c frame)
      = T_Frame g t c frame frame_typing t_typing in
    let x = fresh g in
    let c' = add_frame c frame in
    let C_ST s' = c' in
    let ve: vprop_equiv f g s'.pre pre = ve in
    let s'' = { s' with pre = pre } in
    let c'' = C_ST s'' in
    assert (is_pure_comp (C_ST s'));
    assert (is_pure_comp (C_ST s''));
    assert (comp_post c' == comp_post c'');
    opening_pure_term_with_pure_term (comp_post c') (Tm_Var x) 0;
    opening_pure_term_with_pure_term (comp_post c'') (Tm_Var x) 0;    
    assert (is_pure_term (open_term (comp_post c') x));
    let g' = ((x, Inl (comp_res c'))::g) in
    let ve: vprop_equiv f g (comp_pre c') (comp_pre c'') = ve in    
    let ve' 
      : vprop_equiv f g'
                      (open_term (comp_post c') x)
                      (open_term (comp_post c'') x) = VE_Refl _ _ in
    let st_equiv = ST_VPropEquiv g c' c'' x ve ve' in
    let t_typing = T_Equiv _ _ _ _ t_typing st_equiv in
    (| C_ST s'', t_typing |)
#pop-options

let frame_empty (f:fstar_top_env)
                (g:env)
                (pre:pure_term)
                (pre_typing: tot_typing f g pre Tm_VProp)
                (u:universe)
                (ty:pure_term) 
                (ut:universe_of f g ty u)
                (t:term)
                (c:pure_comp_st{ comp_pre c == Tm_Emp })
                (d:src_typing f g t c)
  : (c:pure_comp_st { comp_pre c == pre} &
     src_typing f g t c)
  = let d = T_Frame g t c pre pre_typing d in
    let c = add_frame c pre in
    let C_ST s = c in
    let d : src_typing f g t c = d in
    let s' = { s with pre = pre } in
    let c' = C_ST s' in
    let x = fresh g in
    let eq : st_equiv f g c c' = ST_VPropEquiv g c c' x (VE_Unit g pre) (VE_Refl _ _) in
    (| c', T_Equiv _ _ _ _ d eq |)
      
#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 10"
let rec check (f:fstar_top_env)
              (g:env)
              (t:term)
              (pre:pure_term)
              (pre_typing: tot_typing f g pre Tm_VProp)
  : T.Tac (c:pure_comp_st { comp_pre c == pre } &
           src_typing f g t c)
  = let frame_empty = frame_empty f g pre pre_typing in
    match t with
    | Tm_BVar _ -> T.fail "not locally nameless"
    | Tm_Var _
    | Tm_FVar _ 
    | Tm_Constant _
    | Tm_PureApp _ _
    | Tm_Let _ _ _ 
    | Tm_Emp
    | Tm_Pure _
    | Tm_Star _ _ 
    | Tm_ExistsSL _ _
    | Tm_ForallSL _ _
    | Tm_Arrow _ _
    | Tm_Type _
    | Tm_VProp ->
      let (| u, ty, uty, d |) = check_tot_univ f g t in
      let c = return_comp u ty t in
      let d = T_Return _ _ _ _ (E d) uty in
      frame_empty u ty uty t c d

    | Tm_Abs t pre_hint body ->
      let (| u, t_typing |) = check_universe f g t in
      let x = fresh g in
      let g' = (x, Inl t) :: g in
      let pre = open_term pre_hint x in
      (
        match check_tot f g' pre with
        | (| Tm_VProp, pre_typing |) ->
          let (| c_body, body_typing |) = check f g' (open_term body x) pre (E pre_typing) in
          let tt = T_Abs g x t u body c_body pre_hint t_typing body_typing in
          let tres = Tm_Arrow t (close_comp c_body x) in
          (* could avoid this re-checking call if we had a lemma about arrow typing *)
          let (| ures, ures_ty |) = check_universe f g tres in
          let c = return_comp_noeq ures tres in
          let d = T_ReturnNoEq _ _ _ _ tt ures_ty in
          frame_empty ures tres ures_ty _ c d
          
        | _ -> T.fail "bad hint"
      )

    | Tm_STApp head arg ->
      let (| ty_head, dhead |) = check_tot f g head in
      let (| ty_arg, darg |) = check_tot f g arg in      
      begin
      match ty_head with
      | Tm_Arrow formal (C_ST res) ->
        if ty_arg <> formal
        then T.fail "Type of formal parameter does not match type of argument"
        else let d = T_STApp g head formal (C_ST res) arg dhead (E darg) in
             opening_pure_comp_with_pure_term (C_ST res) arg 0;
             try_frame_pre pre_typing d
      | _ -> T.fail "Unexpected head type in impure application"
      end

    | Tm_Bind t e1 e2 ->
      let (| c1, d1 |) = check f g e1 pre pre_typing in
      let C_ST s1 = c1 in
      if t <> s1.res 
      then T.fail "Annotated type of let-binding is incorrect"
      else (
        match check_tot f g t with
        | (| Tm_Type u, t_typing |) ->
          if u <> s1.u then T.fail "incorrect universe"
          else (
            let x = fresh g in
            let next_pre = open_term s1.post x in
            let g' = (x, Inl s1.res)::g in
            let next_pre_typing : tot_typing f g' next_pre Tm_VProp =
              //would be nice to prove that this is typable as a lemma,
              //without having to re-check it
              match check_tot f g' next_pre with
              | (| Tm_VProp, nt |) -> E nt
              | _ -> T.fail "next pre is not typable"
            in
            let (| c2, d2 |) = check f g' (open_term e2 x) next_pre next_pre_typing in
            let C_ST s2 = c2 in
            let (| u, res_typing |) = check_universe f g s2.res in
            if u <> s2.u || x `Set.mem` freevars s2.post
            then T.fail "Unexpected universe for result type or variable escapes scope in bind"
            else (
              match check_tot f ((x, Inl s2.res)::g) (open_term s2.post x) with
              | (| Tm_VProp, post_typing |) ->
                let bc : bind_comp f g x c1 c2 _ = (Bind_comp g x c1 c2 res_typing x (E post_typing)) in
                (| _, T_Bind _ _ _ _ _ _ _ d1 (E t_typing) d2 bc |)
              | _ -> T.fail "Ill-typed postcondition in bind"
            )
          )
        | _ -> T.fail "Ill-typed annotated type on `bind`"
     )
    | Tm_If _ _ _ ->
      T.fail "Not handling if yet"
#pop-options

////////////////////////////////////////////////////////////////////////////////
// elaboration of derivations
////////////////////////////////////////////////////////////////////////////////

let mk_return (u:universe) (ty:R.term) (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv return_lid) [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit); (t, R.Q_Explicit)]

let mk_return_noeq (u:universe) (ty:R.term) (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv return_noeq_lid) [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit); (t, R.Q_Explicit)]

let mk_frame (u:universe)
             (ty:R.term)
             (pre: R.term)
             (post: R.term)
             (frame: R.term)
             (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv frame_lid)
                         [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit);
                   (pre, R.Q_Implicit);
                   (post, R.Q_Implicit);
                   (frame, R.Q_Explicit);
                   (t, R.Q_Explicit)]

let mk_sub (u:universe)
           (ty:R.term)
           (pre1 pre2: R.term)
           (post1 post2: R.term)
           (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv subsumption_lid)
                         [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit);
                   (pre1, R.Q_Implicit);
                   (pre2, R.Q_Explicit);                   
                   (post1, R.Q_Implicit);
                   (post2, R.Q_Explicit);                   
                   (t, R.Q_Explicit)]
  
let rec elab_src_typing (#f:fstar_top_env)
                        (#g:env)
                        (#t:term)
                        (#c:pure_comp)
                        (d:src_typing f g t c)
  : Tot R.term (decreases d)
  = match d with
    | T_Tot _ _ _ _ -> elab_pure t

    | T_Abs _ x ty _u body _ _ ty_typing body_typing ->
      let ty = elab_pure ty in
      let body = elab_src_typing body_typing in
      mk_abs ty (RT.close_term body x) //this closure should be provably redundant by strengthening the conditions on x
    
    | T_STApp _ head _formal _res arg head_typing arg_typing ->
      let head = elab_src_typing head_typing in
      let arg = elab_pure arg in
      R.mk_app head [(arg, R.Q_Explicit)]

    | T_Return _ _ ty u _ _ ->
      mk_return u (elab_pure ty) (elab_pure t)

    | T_ReturnNoEq _ _ ty u t_typing _ ->
      mk_return u (elab_pure ty) (elab_src_typing t_typing)

    | T_Bind _ e1 e2 c1 c2 x c e1_typing t_typing e2_typing _bc ->
      let e1 = elab_src_typing e1_typing in
      let e2 = elab_src_typing e2_typing in
      let ty1 = elab_pure (comp_res c1) in
      elab_bind c1 c2 e1 (mk_abs ty1 (RT.close_term e2 x))
      
    | T_Frame _ _ c frame _frame_typing e_typing ->
      let e = elab_src_typing e_typing in
      let C_ST c = c in
      let ty = elab_pure c.res in
      let pre = elab_pure c.pre in
      let post = elab_pure c.post in
      mk_frame c.u ty pre post (elab_pure frame) e
      
    | T_If _ b e1 e2 _c hyp _ e1_typing e2_typing ->
      let b = elab_pure b in
      let e1 = elab_src_typing e1_typing in
      let e2 = elab_src_typing e2_typing in
      let open R in
      pack_ln (Tv_Match b None 
                  [(Pat_Constant C_True, e1);
                   (Pat_Constant C_False, e2)])

    | T_Equiv _ _ c1 c2 e_typing _ ->
      let e = elab_src_typing e_typing in
      let C_ST c1 = c1 in
      let C_ST c2 = c2 in
      let ty = elab_pure c1.res in
      mk_sub c1.u ty
             (elab_pure c1.pre)
             (elab_pure c2.pre)
             (mk_abs ty (elab_pure c1.post))
             (mk_abs ty (elab_pure c2.post))
             e

      
////////////////////////////////////////////////////////////////////////////////
// Main theorem 
////////////////////////////////////////////////////////////////////////////////


let rec extend_env_l_lookup_bvar (g:R.env) (sg:env) (x:var)
  : Lemma 
    (requires (forall x. RT.lookup_bvar g x == None))
    (ensures (
      match lookup sg x with
      | Some b -> RT.lookup_bvar (extend_env_l g sg) x == Some (elab_binding b)
      | None -> RT.lookup_bvar (extend_env_l g sg) x == None))
    (decreases sg)
    [SMTPat (RT.lookup_bvar (extend_env_l g sg) x)]
  = match sg with
    | [] -> ()
    | hd :: tl -> extend_env_l_lookup_bvar g tl x

#push-options "--ifuel 2"
let rec elab_pure_equiv (#f:fstar_top_env)
                        (#g:env)
                        (#t:pure_term)
                        (#c:pure_comp { C_Tot? c })
                        (d:src_typing f g t c)
  : Lemma (ensures elab_src_typing d == elab_pure t)
          (decreases d)
  = match d with
    | T_Tot _ _ _ d -> ()
    | T_If _ _ _ _ _ _ _ d1 d2 -> 
      elab_pure_equiv d1; 
      elab_pure_equiv d2      
#pop-options

let rec elab_open_commute' (e:pure_term)
                           (v:pure_term)
                           (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure e) (RT.OpenWith (elab_pure v)) n ==
              elab_pure (open_term' e v n))
          (decreases e)
  = admit()
and elab_comp_open_commute' (c:pure_comp) (v:pure_term) (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure_comp c) (RT.OpenWith (elab_pure v)) n ==
              elab_pure_comp (open_comp' c v n))
          (decreases c)
  = admit()

let elab_comp_post (c:pure_comp_st) : R.term =
  let t = elab_pure (comp_res c) in
  let post = elab_pure (comp_post c) in
  mk_abs t post

let comp_post_type (c:pure_comp_st) : R.term = 
  let t = elab_pure (comp_res c) in
  mk_tot_arrow1 (t, R.Q_Explicit) vprop_tm
  

assume
val inversion_of_stt_typing (f:fstar_top_env) (g:env) (c:pure_comp_st)
                            (u:R.universe)
                            // _ |- stt u#u t pre (fun (x:t) -> post) : Type _ 
                            (_:RT.typing (extend_env_l f g) (elab_pure_comp c) (RT.tm_type u))
  : GTot ( // _ |- t : Type u#u
          RT.typing (extend_env_l f g) (elab_pure (comp_res c)) (RT.tm_type (elab_universe (comp_u c))) &
          // _ |- pre : vprop
          RT.typing (extend_env_l f g) (elab_pure (comp_pre c)) (elab_pure (Tm_VProp)) &
          // _ |- (fun (x:t) -> post) : t -> vprop
          RT.typing (extend_env_l f g) (elab_comp_post c)
                                       (elab_pure (Tm_Arrow (comp_res c) (C_Tot Tm_VProp))))
          

#push-options "--fuel 8 --ifuel 4 --z3rlimit_factor 10"
let rec elab_close_commute' (e:pure_term)
                            (v:var)
                            (n:index)
  : Lemma (ensures (
              closing_pure_term e v n;
              RT.open_or_close_term' (elab_pure e) (RT.CloseVar v) n ==
              elab_pure (close_term' e v n)))
          (decreases e)
  = closing_pure_term e v n;
    match e with
    | Tm_BVar _ 
    | Tm_Var _ 
    | Tm_FVar _
    | Tm_Constant _
    | Tm_Emp 
    | Tm_Type _ 
    | Tm_VProp -> ()
    | Tm_PureApp e1 e2 ->
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v n
    | Tm_Let t e1 e2 ->
      elab_close_commute' t v n;    
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v (n + 1)
    | Tm_Pure p ->
      elab_close_commute' p v n
    | Tm_Star e1 e2 ->
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v n
    | Tm_ExistsSL t body
    | Tm_ForallSL t body ->
      elab_close_commute' t v n;
      elab_close_commute' body v (n + 1)    
    | Tm_Arrow t body ->
      elab_close_commute' t v n;
      elab_comp_close_commute' body v (n + 1)
    | Tm_If e1 e2 e3 ->
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v n;
      elab_close_commute' e3 v n

and elab_comp_close_commute' (c:pure_comp) (v:var) (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure_comp c) (RT.CloseVar v) n ==
              elab_pure_comp (close_comp' c v n))
          (decreases c)
  = match c with
    | C_Tot t -> elab_close_commute' t v n
    | C_ST s -> 
      elab_close_commute' s.res v n;
      elab_close_commute' s.pre v n;
      elab_close_commute' s.post v (n + 1)           
#pop-options

let elab_comp_close_commute (c:pure_comp) (x:var)
  : Lemma (elab_pure_comp (close_pure_comp c x) == RT.close_term (elab_pure_comp c) x)
  = RT.close_term_spec (elab_pure_comp c) x;
    elab_comp_close_commute' c x 0

let elab_comp_open_commute (c:pure_comp) (x:pure_term)
  : Lemma (elab_pure_comp (open_comp_with c x) == RT.open_with (elab_pure_comp c) (elab_pure x))
  = RT.open_with_spec (elab_pure_comp c) (elab_pure x);
    elab_comp_open_commute' c x 0

let open_close_inverse (e:R.term { RT.ln e }) (x:var)
  : Lemma (RT.open_term (RT.close_term e x) x == e)
   = RT.close_term_spec e x;
     RT.open_term_spec (RT.close_term e x) x;
     RT.open_close_inverse 0 e x


let rec extend_env_l_lookup_fvar (g:R.env) (sg:env) (fv:R.fv) (us:R.universes)
  : Lemma 
    (ensures
      RT.lookup_fvar_uinst (extend_env_l g sg) fv us ==
      RT.lookup_fvar_uinst g fv us)
    [SMTPat (RT.lookup_fvar_uinst (extend_env_l g sg) fv us)]
  = match sg with
    | [] -> ()
    | hd::tl -> extend_env_l_lookup_fvar g tl fv us

let ty_of x = fst x
let qual_of x = snd x
module L = FStar.List.Tot
let u_unk = (R.pack_universe R.Uv_Unk)

let sub = list (RT.open_or_close & nat)

let shift (s:sub) : sub = L.map #(RT.open_or_close & nat) #(RT.open_or_close & nat) (fun (oc, s) -> oc, s + 1) s

let rec subst (x:R.term) (s:sub)
  : GTot R.term (decreases s)
  = match s with
    | [] -> x
    | (oc,i)::tl -> subst (RT.open_or_close_term' x oc i) tl

let rec merge_subst (x:R.term) (s0 s1:sub)
  : Lemma 
    (ensures subst (subst x s0) s1 == subst x (s0@s1))
    (decreases s0)
    [SMTPat (subst (subst x s0) s1)]
  = match s0 with
    | [] -> ()
    | hd::tl -> merge_subst (subst x [hd]) tl s1

let subst_arrow (hd: (R.term * R.aqualv))
                (res: R.term)
                (s:sub)
    : Lemma (subst (mk_tot_arrow1 hd res) s ==
             mk_tot_arrow1 (subst (fst hd) s, snd hd) (subst res (shift s)))
    = admit()

let app_tot_arrow1 (#hd: (R.term * R.aqualv))
                   (#res: R.term) 
                   (#g:R.env)
                   (#head: R.term)
                   (head_typing: RT.typing g head (mk_tot_arrow1 hd res))
                   (#arg: R.term)
                   (arg_typing: RT.typing g arg (ty_of hd))
  : GTot (RT.typing g (R.mk_app head [arg, qual_of hd])
                      (subst res [RT.OpenWith arg, 0]))
  = let ty,q = hd in
    RT.open_with_spec res arg;
    let d : RT.typing g (R.mk_app head [arg, qual_of hd])
                        (RT.open_or_close_term' res
                                                (RT.OpenWith arg) 0)
        = RT.T_App _ _ _ (binder_of_t_q ty q) res u_unk head_typing arg_typing
    in
    d

let merge_subst_d (#g:R.env) (#head:R.term) (#t:R.term) (#s0 #s1:sub)
                  (d:RT.typing g head (subst (subst t s0) s1))
  : RT.typing g head (subst t (s0 @ s1))
  = merge_subst t s0 s1;
    d

let open_tot_arrow (#formals:list (R.term & R.aqualv) { Cons? formals })
                   (#res:R.term)
                   (#g:R.env) (#e:R.term)
                   (#s:sub)
                   (d:RT.typing g e (subst (mk_tot_arrow formals res) s))
  : RT.typing g e (mk_tot_arrow1 (subst (ty_of (L.hd formals)) s, qual_of (L.hd formals))
                                 (subst (mk_tot_arrow (L.tl formals) res) (shift s)))
  = subst_arrow (L.hd formals) (mk_tot_arrow (L.tl formals) res) s;
    d

let as_tot_arrow1 (#formals:list (R.term & R.aqualv) { Cons? formals })
                  (#res:R.term)
                  (#g:R.env)
                  (#head:R.term)
                  (head_typing: RT.typing g head (mk_tot_arrow formals res))
  : RT.typing g head (mk_tot_arrow1 (L.hd formals) (mk_tot_arrow (L.tl formals) res))
  = head_typing


#push-options "--query_stats"
let app_typing (#formals:list (R.term & R.aqualv) { Cons? formals })
               (#res:R.term)
               (#g:R.env)
               (#s:sub)
               (#head:R.term)
               (d:RT.typing g head (subst (mk_tot_arrow formals res) s))
               (#arg:R.term)
               (d':RT.typing g arg (subst (ty_of (L.hd formals)) s))
   : GTot (RT.typing g (R.mk_app head [(arg, qual_of (L.hd formals))]) 
                       (subst (mk_tot_arrow (L.tl formals) res) (shift s @ [RT.OpenWith arg, 0])))
   = merge_subst_d (app_tot_arrow1 (open_tot_arrow d) d')

let subst_tm_type_id (u:R.universe) (s:sub) 
  : Lemma (subst (RT.tm_type u) s == RT.tm_type u)
          [SMTPat (subst (RT.tm_type u) s)]
  = admit()

let subst_tm_vprop (s:sub) 
  : Lemma (subst vprop_tm s == vprop_tm)
          [SMTPat (subst vprop_tm s)]
  = admit()

#push-options "--fuel 2 --ifuel 1"

let rec ln' (t:term) (i:int) =
  match t with
  | Tm_BVar j -> j <= i
  | Tm_Var _
  | Tm_FVar _
  | Tm_Constant _  
  | Tm_Emp
  | Tm_Type _
  | Tm_VProp -> true

  | Tm_Abs t pre_hint body ->
    ln' t i &&
    ln' pre_hint (i + 1) &&
    ln' body (i + 1)

  | Tm_STApp t1 t2
  | Tm_PureApp t1 t2
  | Tm_Star t1 t2 ->
    ln' t1 i &&
    ln' t2 i

  | Tm_Let t e1 e2
  | Tm_Bind t e1 e2 ->
    ln' t i &&
    ln' e1 i &&
    ln' e2 (i + 1)

  | Tm_Pure p ->
    ln' p i

  | Tm_ExistsSL t body
  | Tm_ForallSL t body ->
    ln' t i &&
    ln' t (i + 1)
    
  | Tm_Arrow t c ->
    ln' t i &&
    ln'_comp c (i + 1)
    
  | Tm_If b then_ else_ ->
    ln' b i &&
    ln' then_ i &&
    ln' else_ i

and ln'_comp (c:comp) (i:int)
  : Tot bool
  = match c with
    | C_Tot t -> ln' t i
    | C_ST st -> 
      ln' st.res i &&
      ln' st.pre i &&
      ln' st.post (i + 1)

let ln (t:term) = ln' t (-1)
let ln_c (c:comp) = ln'_comp c (-1)
let ln_comp = c:pure_comp_st{ ln_c c }

let rec close_open_inverse (t:term) (x:var { ~(x `Set.mem` freevars t) } )
  : Lemma (ensures close_term (open_term t x) x== t)
          (decreases t)
  = admit()

let equiv_arrow (g:R.env) (t1:R.term) (u2:R.universe) (t2:R.term) (pre:R.term) (post:R.term) //need some ln preconditions
  : GTot (RT.equiv g (mk_tot_arrow1 (t1, R.Q_Explicit)
                                    (mk_stt_app u2 [t2; pre; post]))
                     (mk_tot_arrow1 (t1, R.Q_Explicit)
                                    (mk_stt_app u2 [t2; R.mk_app (mk_abs t1 pre) [bound_var 0, R.Q_Explicit]; post])))
  = admit()
  

#push-options "--z3rlimit_factor 5"
let elab_bind_typing (f:fstar_top_env)
                     (g:env)
                     (c1 c2 c:ln_comp)
                     (x:var { ~ (x `Set.mem` freevars_comp c1) })
                     (r1:R.term)
                     (r1_typing: RT.typing (extend_env_l f g) r1 (elab_pure_comp c1))
                     (r2:R.term)
                     (r2_typing: RT.typing (extend_env_l f g) r2 
                                           (elab_pure (Tm_Arrow (comp_res c1) (close_pure_comp c2 x))))
                     (bc:bind_comp f g x c1 c2 c)
                     (t2_typing : RT.typing (extend_env_l f g) (elab_pure (comp_res c2)) (RT.tm_type (elab_universe (comp_u c2))))
                     (post2_typing: RT.typing (extend_env_l f g) (elab_comp_post c2) (post2_type_bind (elab_pure (comp_res c2)))) 
  : GTot (RT.typing (extend_env_l f g) (elab_bind c1 c2 r1 r2) (elab_pure_comp c))
  = let rg = extend_env_l f g in
    let u1 = elab_universe (comp_u c1) in
    let u2 = elab_universe (comp_u c2) in
    let head = bind_univ_inst u1 u2 in
    assert (RT.lookup_fvar_uinst rg bind_fv [u1; u2] == Some (bind_type u1 u2));
    let head_typing : RT.typing _ _ (bind_type u1 u2) = RT.T_UInst rg bind_fv [u1;u2] in
    let (| _, c1_typing |) = RT.type_correctness _ _ _ r1_typing in
    let t1_typing, pre_typing, post_typing = inversion_of_stt_typing _ _ _ _ c1_typing in
    let t1 = (elab_pure (comp_res c1)) in
    let t2 = (elab_pure (comp_res c2)) in
    let t1_typing : RT.typing rg t1 (RT.tm_type u1) = t1_typing in
    let post1 = elab_comp_post c1 in
    let c2_x = close_pure_comp c2 x in
    assume (comp_res c2_x == comp_res c2);
    assume (comp_post c2_x == comp_post c2);    
    assert (open_term (comp_post c1) x == comp_pre c2);
    assert (~ (x `Set.mem` freevars (comp_post c1)));
    close_open_inverse (comp_post c1) x;
    assert (comp_post c1 == close_term (comp_pre c2) x);
    assert (post1 == mk_abs t1 (elab_pure (comp_post c1)));
    assert (elab_pure (comp_post c1) == elab_pure (comp_pre (close_pure_comp c2 x)));
    //ln (comp_post c1) 0
    let g_typing
      : RT.typing _ _ 
                  (mk_tot_arrow1 (t1, R.Q_Explicit)
                                 (mk_stt_app u2 [t2; elab_pure (comp_post c1); elab_comp_post c2]))
      = r2_typing in
    let g_typing 
      : RT.typing _ _ 
                  (mk_tot_arrow1 (t1, R.Q_Explicit)
                                 (mk_stt_app u2 [t2; R.mk_app (mk_abs t1 (elab_pure (comp_post c1))) [bound_var 0, R.Q_Explicit]; elab_comp_post c2]))
      = RT.(T_Sub _ _ _ _ r2_typing (ST_Equiv _ _ _ (equiv_arrow _ _ _ _ _ _))) in
    let d : RT.typing _ (elab_bind c1 c2 r1 r2) _ = 
       inst_bind_g 
        (inst_bind_f
          (inst_bind_post2
            (inst_bind_post1
              (inst_bind_pre 
                (inst_bind_t2 
                  (inst_bind_t1 head_typing t1_typing)
                  t2_typing)
                pre_typing)
              post_typing)
            post2_typing)
          r1_typing)
        g_typing
    in
    d

#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 8"
let rec soundness (f:fstar_top_env)
                  (g:env)
                  (t:term)
                  (c:pure_comp)
                  (d:src_typing f g t c)
  : GTot (RT.typing (extend_env_l f g) (elab_src_typing d) (elab_pure_comp c))
         (decreases d)
  = let mk_t_abs (#u:universe)
                 (#ty:pure_term)
                 (t_typing:tot_typing f g ty (Tm_Type u) { t_typing << d })
                 (#body:term)
                 (#x:var { None? (lookup g x) })
                 (#c:pure_comp)
                 (body_typing:src_typing f ((x, Inl ty)::g) (open_term body x) c { body_typing << d })
      : GTot (RT.typing (extend_env_l f g)
                        (mk_abs (elab_pure ty) (RT.close_term (elab_src_typing body_typing) x))
                        (elab_pure (Tm_Arrow ty (close_pure_comp c x))))
      = let E t_typing = t_typing in
        let r_ty = elab_pure ty in
        let r_body = elab_src_typing body_typing in
        let r_c = elab_pure_comp c in
        let r_t_typing = soundness _ _ _ _ t_typing in
        elab_pure_equiv t_typing;
        let r_body_typing = soundness _ _ _ _ body_typing in
        RT.well_typed_terms_are_ln _ _ _ r_body_typing;
        open_close_inverse r_body x;
        elab_comp_close_commute c x;      
        RT.T_Abs (extend_env_l f g)
                   x
                   r_ty
                   (RT.close_term r_body x)
                   r_c
                   (elab_universe u) _ _
                   r_t_typing
                   r_body_typing
    in
    match d with
    | T_Tot _ _ _ d -> d

    | T_Abs _ x ty u body c hint t_typing body_typing ->
      mk_t_abs t_typing body_typing

    | T_STApp _ head formal res arg head_typing arg_typing ->
      let E arg_typing = arg_typing in
      let r_head = elab_src_typing head_typing in
      let r_arg = elab_pure arg in
      elab_pure_equiv arg_typing;
      let r_head_typing
        : RT.typing _ r_head (elab_pure (Tm_Arrow formal res))
        = soundness _ _ _ _ head_typing
      in
      let r_arg_typing = soundness _ _ _ _ arg_typing in
      elab_comp_open_commute res arg;
      RT.T_App _ _ _ (binder_of_t_q (elab_pure formal) R.Q_Explicit)
                     (elab_pure_comp res)
                     ((R.pack_universe R.Uv_Unk))
                     r_head_typing
                     r_arg_typing

    | T_Bind _ e1 e2 c1 c2 x c e1_typing t_typing e2_typing bc ->
      let r1_typing
        : RT.typing _ _ (elab_pure_comp c1)
        = soundness _ _ _ _ e1_typing
      in
      let r2_typing
        : RT.typing _ _ (elab_pure (Tm_Arrow (comp_res c1) (close_pure_comp c2 x)))
        = mk_t_abs t_typing e2_typing
      in
      let e = elab_src_typing d in
      let Bind_comp _ _ _ _ (E t2_typing) y (E post2_typing) = bc in
      elab_pure_equiv t2_typing;
      elab_pure_equiv post2_typing;      
      let post2_typing 
        : RT.typing _ (mk_abs (elab_pure (comp_res c2)) 
                              (RT.close_term (elab_src_typing post2_typing) y))
                      (post2_type_bind (elab_pure (comp_res c2)))                              
        = mk_t_abs (E t2_typing) post2_typing in
      let post2_typing 
        : RT.typing _ (mk_abs (elab_pure (comp_res c2)) 
                              (RT.close_term (elab_pure (open_term (comp_post c2) y)) y))
                      (post2_type_bind (elab_pure (comp_res c2)))                              
        = post2_typing in
      elab_close_commute' (open_term (comp_post c2) y) y 0;
      RT.close_term_spec (elab_pure (open_term (comp_post c2) y)) y;
      assert (RT.close_term (elab_pure (open_term (comp_post c2) y)) y ==
              elab_pure (close_term (open_term (comp_post c2) y) y));
      let post2_typing 
        : RT.typing _ (mk_abs (elab_pure (comp_res c2)) 
                              (elab_pure (close_term (open_term (comp_post c2) y) y)))
                      (post2_type_bind (elab_pure (comp_res c2)))                              
        = post2_typing in
      assume (~ (y `Set.mem` freevars_comp c2));
      close_open_inverse (comp_post c2) y;
      let post2_typing 
        : RT.typing _ (elab_comp_post c2)
                      (post2_type_bind (elab_pure (comp_res c2)))                              
        = post2_typing in
      let t2_typing = soundness _ _ _ _ t2_typing in
      assume (~ (x `Set.mem` freevars_comp c1));
      assume (ln_c c1 /\ ln_c c2 /\ ln_c c);
      elab_bind_typing f g _ _ _ x _ r1_typing _ r2_typing bc t2_typing post2_typing
      
    | _ -> admit()
  
