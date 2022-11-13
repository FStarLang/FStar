module MiniSteel
module RT = Refl.Typing
module R = FStar.Reflection
open FStar.List.Tot
  
type lident = R.name

let bool_lid = ["Prims"; "bool"]
let vprop_lid = ["Steel"; "Effect"; "Common"; "vprop"]
let emp_lid = ["Steel"; "Effect"; "Common"; "emp"]
let star_lid = ["Steel"; "Effect"; "Common"; "star"]
let pure_lid = ["Steel"; "ST"; "Util"; "pure"]
let exists_lid = ["Steel"; "ST"; "Util"; "exists_"]
let forall_lid = ["Steel"; "ST"; "Util"; "forall_"]
let st_thunk_t_lid = ["Steel"; "ST"; "Util"; "stt"] //the thunked, value-type counterpart of the effect STT

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

let fstar_env =
  g:R.env { 
    RT.lookup_fvar g RT.bool_fv == Some (RT.tm_type RT.u_zero)
    ///\ vprop etc
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

assume
val dummy_range : Prims.range 
let rec elab_universe (u:universe)
  : Tot R.universe
  = match u with
    | U_zero -> R.pack_universe (R.Uv_Zero)
    | U_succ u -> R.pack_universe (R.Uv_Succ (elab_universe u))
    | U_var x -> R.pack_universe (R.Uv_Name (x, dummy_range))
    | U_max u1 u2 -> R.pack_universe (R.Uv_Max [elab_universe u1; elab_universe u2])

let mk_st (u:universe) (res pre post:R.term)
  : Tot R.term 
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv vprop_lid) [elab_universe u]) in
    R.mk_app head [(res, R.Q_Explicit); (pre, R.Q_Explicit); (post, R.Q_Explicit)]

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
      Some (R.pack_ln 
              (R.Tv_Arrow 
                (RT.as_binder 0 t) 
                (R.pack_comp (R.C_Total c (R.pack_universe R.Uv_Unk) []))))

    | Tm_Abs t _ e ->
      let? t = elab_term t in
      let? e = elab_term e in
      Some (R.pack_ln (R.Tv_Abs (RT.as_binder 0 t) e))

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
      let body = R.pack_ln (R.Tv_Abs (RT.as_binder 0 t) b) in
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

    | Tm_Abs t pre_hint body ->
      aux t i;
      aux body (i + 1)

    | Tm_PureApp l r
    | Tm_STApp l r
    | Tm_Star l r ->    
      aux l i; aux r i
                 
    | Tm_Let t e1 e2 
    | Tm_Bind t e1 e2 ->    
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

    | Tm_Abs t pre_hint body ->
      aux t i;
      aux body (i + 1)

    | Tm_PureApp l r
    | Tm_STApp l r
    | Tm_Star l r ->    
      aux l i; aux r i
                 
    | Tm_Let t e1 e2 
    | Tm_Bind t e1 e2 ->    
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

let comp_post (c:pure_comp_st) = let C_ST s = c in s.post

let comp_res (c:comp) : term =
  match c with
  | C_Tot ty -> ty
  | C_ST c -> c.res

let comp_u (c:pure_comp_st) = let C_ST s = c in s.u

[@@erasable]
noeq
type bind_comp (f:fstar_top_env) : env -> pure_comp -> var -> pure_comp -> pure_comp -> Type =
  | Bind_comp :
      g:env ->
      c1:pure_comp_st ->
      x:var ->
      c2:pure_comp_st {
        open_term (comp_post c1) x == comp_pre c2 /\
        ~(x `Set.mem` freevars (comp_post c2)) /\
        ~(x `Set.mem` freevars (comp_res c2)) 
      } ->
      bind_comp f g c1 x  c2 (C_ST {u = comp_u c2; res = comp_res c1; pre = comp_pre c1; post=comp_post c2})

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

  | VE_Ex:
     g:env ->
     x:var { None? (lookup_ty g x) } ->
     ty:pure_term ->
     t0:pure_term ->
     t1:pure_term ->
     vprop_equiv f ((x, Inl ty)::g) (open_term t0 x) (open_term t1 x) ->
     vprop_equiv f g (Tm_ExistsSL ty t0) (Tm_ExistsSL ty t1)

  | VE_Fa:
     g:env ->
     x:var { None? (lookup_ty g x) } ->
     ty:pure_term ->
     t0:pure_term ->
     t1:pure_term ->
     vprop_equiv f ((x, Inl ty)::g) (open_term t0 x) (open_term t1 x) ->
     vprop_equiv f g (Tm_ForallSL ty t0) (Tm_ForallSL ty t1)

[@@erasable]
noeq
type st_equiv (f:fstar_top_env) : env -> pure_comp -> pure_comp -> Type =
  | ST_Equiv :
      g:env ->
      c1:pure_comp_st ->
      c2:pure_comp_st { comp_res c1 == comp_res c2 } -> 
      x:var { None? (lookup_ty g x) } ->
      vprop_equiv f g (comp_pre c1) (comp_pre c2) ->
      vprop_equiv f ((x, Inl (comp_res c1))::g) (open_term (comp_post c1) x) (open_term (comp_post c2) x) ->      
      st_equiv f g c1 c2


let add_frame (s:pure_comp_st) (frame:pure_term)
  : pure_comp_st
  = let C_ST s = s in
    C_ST { s with pre = Tm_Star s.pre frame;
                  post = Tm_Star s.post frame }

let close_pure_comp (c:pure_comp) (x:var) : pure_comp = close_comp c x

[@@erasable]
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
      tot_typing f g head (Tm_Arrow formal res) ->
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
      tot_typing f g e t ->
      universe_of f g t u ->
      src_typing f g e (return_comp_noeq u t)

  | T_Bind:
      g:env ->
      e1:term ->
      e2:term ->
      c1:pure_comp ->
      c2:pure_comp ->
      x:var { None? (lookup g x) (*  /\ ~(x `Set.mem` freevars e2) *) } ->
      c:pure_comp ->
      src_typing f g e1 c1 ->
      src_typing f ((x, Inl (comp_res c1))::g) (open_term e2 x) c2 ->
      bind_comp f g c1 x c2 c ->
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
  src_typing f g e (C_Tot t)

and universe_of (f:fstar_top_env) (g:env) (t:term) (u:universe) =
  tot_typing f g t (Tm_Type u)


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

    | VE_Ex g x ty t0 t1 _
    | VE_Fa g x ty t0 t1 _ ->
      //these require inversion of typing on abstractions
      admit()

  
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
        | Some (Tm_Type u) -> (| u, T_Tot _ _ _ tok |)
        | _ -> T.fail "Not typeable as a universe"
      
let check_tot_univ (f:fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(u:universe &
              ty:pure_term &
              universe_of f g ty u &
              tot_typing f g t ty) { is_pure_term t } )
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
              tot_typing f g t ty) { is_pure_term t })
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
    let st_equiv = ST_Equiv g c' c'' x ve ve' in
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
    let eq : st_equiv f g c c' = ST_Equiv g c c' x (VE_Unit g pre) (VE_Refl _ _) in
    (| c', T_Equiv _ _ _ _ d eq |)
      
#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 4"
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
      let d = T_Return _ _ _ _ d uty in
      frame_empty u ty uty t c d

    | Tm_Abs t pre_hint body ->
      let (| u, t_typing |) = check_universe f g t in
      let x = fresh g in
      let g' = (x, Inl t) :: g in
      let pre = open_term pre_hint x in
      (
        match check_tot f g' pre with
        | (| Tm_VProp, pre_typing |) ->
          let (| c_body, body_typing |) = check f g' (open_term body x) pre pre_typing in
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
        else let d = T_STApp g head formal (C_ST res) arg dhead darg in
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
        let x = fresh g in
        let next_pre = open_term s1.post x in
        let g' = (x, Inl s1.res)::g in
        let next_pre_typing : tot_typing f g' next_pre Tm_VProp =
          //would be nice to prove that this is typable as a lemma,
          //without having to re-check it
          match check_tot f g' next_pre with
          | (| Tm_VProp, nt |) -> nt
          | _ -> T.fail "next pre is not typable"
        in
        let (| c2, d2 |) = check f g' (open_term e2 x) next_pre next_pre_typing in
        let C_ST s2 = c2 in
        if x `Set.mem` freevars s2.post
        ||  x `Set.mem` freevars s2.res
        then T.fail "Let-bound variable escapes its scope"
        else (| _, T_Bind _ _ _ _ _ _ _ d1 d2 (Bind_comp _ c1 _ c2) |)
     )

    | Tm_If _ _ _ ->
      T.fail "Not handling if yet"

////////////////////////////////////////////////////////////////////////////////
// elaboration of derivations
////////////////////////////////////////////////////////////////////////////////
