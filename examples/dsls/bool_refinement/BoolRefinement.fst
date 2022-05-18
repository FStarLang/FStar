module BoolRefinement
module T = FStar.Tactics
module R = FStar.Reflection
module L = FStar.List.Tot

let var = nat
let index = nat

let tun = R.pack_ln R.Tv_Unknown

type src_exp =
  | EBVar : index -> src_exp
  | EVar  : var -> src_exp
  | EBool : bool -> src_exp
  | EIf   : src_exp -> src_exp -> src_exp -> src_exp
  | ELam  : src_ty -> src_exp -> src_exp
  | EApp  : src_exp -> src_exp -> src_exp

and src_ty =
  | TBool : src_ty
  | TRefineBool : src_exp -> src_ty
  | TArrow : src_ty -> src_ty -> src_ty

let rec size (e:src_exp)
  : nat
  = match e with
    | EBool _
    | EBVar _ 
    | EVar _ -> 1
    | EIf b e1 e2 -> size b + size e1 + size e2 + 1
    | ELam _ e -> 1 + size e
    | EApp e1 e2 -> 1 + size e1 + size e2

let rec ln' (e:src_exp) (n:int)
  : bool
  = match e with
    | EBool _
    | EVar _ -> true
    | EBVar m -> m <= n
    | EIf b e1 e2 -> ln' b n && ln' e1 n && ln' e2 n
    | ELam t e -> ln_ty t && ln' e (n + 1)
    | EApp e1 e2 -> ln' e1 n && ln' e2 n
and ln_ty (e:src_ty )
  : bool
  = match e with
    | TBool -> true
    | TRefineBool e -> ln' e (- 1)
    | TArrow t1 t2 -> ln_ty t1 && ln_ty t2

let ln e = ln' e (-1)


let rec open_exp' (e:src_exp) (v:var) (n:index)
  : e':src_exp { size e == size e'}
    = match e with
    | EBool _ -> e
    | EVar m -> EVar m
    | EBVar m -> if m = n then EVar v else EBVar m
    | EIf b e1 e2 -> EIf (open_exp' b v n) (open_exp' e1 v n) (open_exp' e2 v n)
    | ELam t e -> ELam t (open_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (open_exp' e1 v n) (open_exp' e2 v n)

let rec close_exp' (e:src_exp) (v:var) (n:nat)
  : e':src_exp { size e == size e'}
  = match e with
    | EBool _ -> e
    | EVar m -> if m = v then EBVar n else EVar m
    | EBVar m -> EBVar m
    | EIf b e1 e2 -> EIf (close_exp' b v n) (close_exp' e1 v n) (close_exp' e2 v n)
    | ELam t e -> ELam t (close_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (close_exp' e1 v n) (close_exp' e2 v n)

let open_exp e v = open_exp' e v 0
let close_exp e v = close_exp' e v 0

let rec open_close' (e:src_exp) (x:var) (n:nat { ln' e (n - 1) })
  : Lemma (open_exp' (close_exp' e x n) x n == e)
  = match e with
    | EBool _ -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | EIf b e1 e2 -> 
      open_close' b x n;
      open_close' e1 x n;
      open_close' e2 x n
    | ELam _ e -> open_close' e x (n + 1)
    | EApp e1 e2 -> 
      open_close' e1 x n; 
      open_close' e2 x n

let open_close (e:src_exp) (x:var)
  : Lemma 
    (requires ln e)
    (ensures open_exp (close_exp e x) x == e)
    [SMTPat (open_exp (close_exp e x) x)]
  = open_close' e x 0

let rec open_exp_ln (e:src_exp) (v:var) (n:index) (m:int)
  : Lemma 
    (requires ln' e n /\
              m == n - 1)
    (ensures ln' (open_exp' e v n) m)
    [SMTPat (ln' e n);
     SMTPat (ln' (open_exp' e v n) m)]
  = match e with
    | EBool _ -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | EIf b e1 e2 ->
      open_exp_ln b v n m;
      open_exp_ln e1 v n m;
      open_exp_ln e2 v n m
    | ELam _ e -> open_exp_ln e v (n + 1) (m + 1)
    | EApp e1 e2 -> open_exp_ln e1 v n m; open_exp_ln e2 v n m

let rec close_exp_ln (e:src_exp) (v:var) (n:nat)
  : Lemma 
    (requires ln' e (n - 1))
    (ensures ln' (close_exp' e v n) n)
    [SMTPat (ln' (close_exp' e v n) n)]
  = match e with
    | EBool _ -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | EIf b e1 e2 ->
      close_exp_ln b v n;
      close_exp_ln e1 v n;
      close_exp_ln e2 v n
    | ELam _ e -> close_exp_ln e v (n + 1)
    | EApp e1 e2 -> close_exp_ln e1 v n; close_exp_ln e2 v n


let src_eqn = src_exp & src_exp

//environment binds types or equations
let src_env = list (var & either src_ty src_eqn) 

let rec lookup (e:list (var & 'a)) (x:var)
  : option 'a
  = match e with
    | [] -> None
    | (y, v) :: tl -> if x = y then Some v else lookup tl x

let lookup_ty (e:src_env) (x:var)
  : option src_ty
  = match lookup e x with
    | Some (Inl t) -> Some t
    | _ -> None
    
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

let fresh_is_fresh (e:src_env)
  : Lemma (None? (lookup e (fresh e)))
  =  match lookup e (fresh e) with
     | None -> ()
     | Some _ ->
       lookup_mem e (fresh e);
       FStar.Classical.forall_intro (fresh_not_mem e)

[@@erasable]
noeq
type sub_typing : src_env -> src_ty -> src_ty -> Type =
  | S_Refl : g:src_env -> t:src_ty -> sub_typing g t t

[@@erasable]
noeq
type src_typing : src_env -> src_exp -> src_ty -> Type =
  | T_Bool :
      g:src_env ->
      b:bool ->
      src_typing g (EBool b) TBool
  
  | T_Var  :
      g:src_env ->
      x:var { Some? (lookup_ty g x) } ->
      src_typing g (EVar x) (Some?.v (lookup_ty g x))

  | T_Lam  :
      g:src_env ->
      t:src_ty ->
      e:src_exp ->
      t':src_ty ->
      x:var { None? (lookup g x) } ->
      src_ty_ok g t ->
      src_typing ((x, Inl t) :: g) (open_exp e x) t' ->
      src_typing g (ELam t e) (TArrow t t')

  | T_App  :
      g:src_env ->
      e1:src_exp ->
      e2:src_exp ->
      t:src_ty ->
      t':src_ty ->
      t0:src_ty ->
      src_typing g e1 (TArrow t t') ->
      src_typing g e2 t0 ->
      sub_typing g t0 t ->
      src_typing g (EApp e1 e2) t'

   | T_If :
       g:src_env ->
       b:src_exp ->
       e1:src_exp ->
       e2:src_exp ->
       t1:src_ty ->
       t2:src_ty ->
       t:src_ty ->
       hyp:var { None? (lookup g hyp) } ->
       src_typing g b TBool ->
       src_typing ((hyp, Inr (b, EBool true)) :: g) e1 t1 ->
       src_typing ((hyp, Inr (b, EBool false)) :: g) e2 t2 ->
       sub_typing ((hyp, Inr (b, EBool true)) :: g) t1 t ->
       sub_typing ((hyp, Inr (b, EBool false)) :: g) t2 t ->
       src_typing g (EIf b e1 e2) t
       
and src_ty_ok : src_env -> src_ty -> Type =
  | OK_TBool  : g:src_env -> src_ty_ok g TBool
  | OK_TArrow : g:src_env -> t:src_ty -> t':src_ty ->
                src_ty_ok g t ->
                src_ty_ok g t' ->                
                src_ty_ok g (TArrow t t')
  | OK_TRefine: g:src_env ->
                e:src_exp ->
                src_typing [] e (TArrow TBool TBool) ->
                src_ty_ok g (TRefineBool e)

let s_height #g #t0 #t1 (d:sub_typing g t0 t1)
  : GTot nat
  = 1
  
let rec height #g #e #t (d:src_typing g e t)
  : GTot nat (decreases d)
  = match d with
    | T_Bool _ _ -> 1
    | T_Var _ _ -> 1
    | T_Lam _ _ _ _ _ ty_ok body -> max (height body) (t_height ty_ok) + 1
    | T_App _ _ _ _ _ _  tl tr ts -> max (max (height tl) (height tr)) (s_height ts) + 1
    | T_If _ _ _ _ _ _ _ _ tb tl tr sl sr ->
      max (height tb) 
          (max (max (height tl) (height tr))
               (max (s_height sl) (s_height sr))) + 1
    
and t_height (#g:src_env) (#t:src_ty) (d:src_ty_ok g t)    
  : GTot nat (decreases d)
  = match d with
    | OK_TBool _ -> 1
    | OK_TArrow _ _ _ d0 d1 -> max (t_height d0) (t_height d1) + 1
    | OK_TRefine _ _ d -> height d + 1

let check_sub_typing (g:R.env) 
                     (sg:src_env)
                     (t0 t1:src_ty)
  : T.Tac (sub_typing sg t0 t1)
  = if t0 = t1 then S_Refl _ t0
    else T.fail "Not subtypes"

let weaken (g:R.env) (sg:src_env) (hyp:var) (b:src_exp) (t0 t1:src_ty)
  : T.Tac (t:src_ty &
           sub_typing ((hyp,Inr(b, EBool true))::sg) t0 t &
           sub_typing ((hyp,Inr(b, EBool false))::sg) t1 t)
  = if t0 = t1
    then (| t0, S_Refl _ t0, S_Refl _ t1 |)
    else T.fail "weaken is very dumb"
  
let rec check (g:R.env)
              (sg:src_env)
              (e:src_exp { ln e })
  : T.Tac (e':src_exp { ln e' } &
           t':src_ty &
           src_typing sg e' t')
  = match e with
    | EBool b ->
      (| e , TBool, T_Bool _ b |)

    | EVar n ->
      begin
      match lookup_ty sg n with
      | None -> T.fail "Ill-typed"
      | Some t ->
        let d = T_Var sg n in
        (| EVar n, t, d |)
      end

    | ELam t e ->
      let (| t, t_ok |) = check_ty g sg t in
      let x = fresh sg in
      fresh_is_fresh sg;
      let (| e, tbody, dbody |) = check g ((x, Inl t)::sg) (open_exp e x) in
      (| ELam t (close_exp e x), 
         TArrow t tbody, 
         T_Lam sg t (close_exp e x) tbody x t_ok dbody |)

    | EApp e1 e2 ->
      let (| e1, t1, d1 |) = check g sg e1  in
      let (| e2, t2, d2 |) = check g sg e2 in
      begin
      match t1 with
      | TArrow t_arg t_res ->
        let st_ok = check_sub_typing g sg t2 t_arg in
        (| EApp e1 e2, t_res, T_App _ _ _ t_arg t_res _ d1 d2 st_ok |)

      | _ -> 
        T.fail "Expected a function"
      end

    | EIf b e1 e2 ->
      let (| b, tb, ok_b |) = check g sg b in
      let hyp = fresh sg in
      fresh_is_fresh sg;
      if tb = TBool
      then (
        let (| e1, t1, ok_1 |) = check g ((hyp, Inr(b, EBool true))::sg) e1 in
        let (| e2, t2, ok_2 |) = check g ((hyp, Inr(b, EBool false))::sg) e2 in      
        let (| t, w1, w2 |) = weaken g sg hyp b t1 t2 in
        (| EIf b e1 e2, t, T_If _ _ _ _ _ _ _ hyp ok_b ok_1 ok_2 w1 w2 |)
      )
      else T.fail "Branching on a non-boolean"

and check_ty (g:R.env)
             (sg:src_env)
             (t:src_ty{ln_ty t})
  : T.Tac (t':src_ty { ln_ty t' } &
           src_ty_ok sg t')
  = match t with
    | TBool -> (| t, OK_TBool _ |)

    | TArrow t t' ->
      let (| t, t_ok |) = check_ty g sg t in
      let (| t', t'_ok |) = check_ty g sg t' in      
      (| TArrow t t', OK_TArrow _ _ _ t_ok t'_ok |)
      
    | TRefineBool e ->
      let (| e, te, de |) = check g [] e in
      match te with
      | TArrow TBool TBool -> (| TRefineBool e, OK_TRefine _ _ de |)
      | _ -> T.fail "Ill-typed refinement"
  

module RT = Refl.Typing


let b2t_lid : R.name = ["Prims"; "b2t"]
let b2t_fv : R.fv = R.pack_fv b2t_lid
let b2t_ty : R.term = R.(pack_ln (Tv_Arrow (RT.as_binder 0 RT.bool_ty) (RT.mk_total RT.tm_type)))
let r_b2t (t:R.term) 
  : R.term 
  = R.(pack_ln (Tv_App (pack_ln (Tv_FVar b2t_fv)) (t, Q_Explicit)))

let rec elab_exp (e:src_exp)
  : Tot R.term
  = let open R in
    match e with
    | EBool true ->
      pack_ln (Tv_Const R.C_True)

    | EBool false ->
      pack_ln (Tv_Const R.C_False)

    | EBVar n -> 
      let bv = R.pack_bv (RT.make_bv n tun) in
      R.pack_ln (Tv_BVar bv)
      
    | EVar n ->
      // tun because type does not matter at a use site
      let bv = R.pack_bv (RT.make_bv n tun) in
      R.pack_ln (Tv_Var bv)

    | ELam t e ->
      let t = elab_ty t in
      let e = elab_exp e in
      R.pack_ln (Tv_Abs (RT.as_binder 0 t) e)
             
    | EApp e1 e2 ->
      let e1 = elab_exp e1 in
      let e2 = elab_exp e2 in
      R.pack_ln (Tv_App e1 (e2, Q_Explicit))

    | EIf b e1 e2 ->
      let b = elab_exp b in
      let e1 = elab_exp e1 in
      let e2 = elab_exp e2 in
      R.pack_ln (Tv_Match b None [(Pat_Constant C_True, e1); (Pat_Constant C_False, e2)])
      
and elab_ty (t:src_ty) 
  : R.term  
  = let open R in
    match t with
    | TBool -> 
      RT.bool_ty
      
    | TArrow t1 t2 ->
      let t1 = elab_ty t1 in
      let t2 = elab_ty t2 in
      R.pack_ln 
        (R.Tv_Arrow 
          (RT.as_binder 0 t1)
          (R.pack_comp (C_Total t2 [])))
          
    | TRefineBool e ->
      let e = elab_exp e in
      let bv = R.pack_bv (RT.make_bv 0 RT.bool_ty) in
      let refinement = r_b2t (R.pack_ln (Tv_App e (R.pack_ln (Tv_BVar bv), Q_Explicit))) in
      R.pack_ln (Tv_Refine bv refinement)

let elab_eqn (e1 e2:src_exp)
  : R.term
  = RT.eq2 RT.bool_ty (elab_exp e1) (elab_exp e2)

let binding = either src_ty src_eqn
let elab_binding (b:binding)
  : R.term 
  = match b with
    | Inl t -> elab_ty t
    | Inr (e1, e2) -> elab_eqn e1 e2
    
let extend_env_l (g:R.env) (sg:src_env) = 
  L.fold_right 
    (fun (x, b) g ->  RT.extend_env g x (elab_binding b))
     sg
     g

let rec extend_env_l_lookup_bvar (g:R.env) (sg:src_env) (x:var)
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

let elab_open_commute (e:src_exp) (x:var)
  : Lemma (RT.open_term (elab_exp e) x == elab_exp (open_exp e x))
          [SMTPat (RT.open_term (elab_exp e) x)]
  = admit()

//key lemma about STLC types
let src_types_are_closed1 (ty:src_ty) (v:R.term)
  : Lemma (RT.open_with (elab_ty ty) v == elab_ty ty)
          [SMTPat (RT.open_with (elab_ty ty) v)]
  = admit()

let src_types_are_closed2 (ty:src_ty) (x:R.var)
  : Lemma (RT.close_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.close_term (elab_ty ty) x)]
  = admit()


let src_types_are_closed3 (ty:src_ty) (x:R.var)
  : Lemma (RT.open_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.open_term (elab_ty ty) x)]
  = admit()

let fstar_env =
  g:R.env { 
    RT.lookup_fvar g RT.bool_fv == Some RT.tm_type /\
    RT.lookup_fvar g b2t_fv == Some b2t_ty
  }

let fstar_top_env =
  g:fstar_env { 
    forall x. None? (RT.lookup_bvar g x )
  }

let b2t_typing (g:fstar_env) (t:R.term) (dt:RT.typing g t RT.bool_ty)
  : RT.typing g (r_b2t t) RT.tm_type
  = let b2t_typing : RT.typing g _ b2t_ty = RT.T_FVar g b2t_fv in
    let app_ty : _ = RT.T_App _ _ _ _ _ b2t_typing dt in
    assume (RT.open_with RT.tm_type t == RT.tm_type);
    app_ty

let extend_env_l_lookup_fvar (g:R.env) (sg:src_env) (fv:R.fv)
  : Lemma 
    (ensures
      RT.lookup_fvar (extend_env_l g sg) fv ==
      RT.lookup_fvar g fv)
    [SMTPat (RT.lookup_fvar (extend_env_l g sg) fv)]
  = admit()
open FStar.List.Tot    
let rec src_ty_ok_weakening (sg sg':src_env) 
                            (x:var { None? (lookup sg x) && None? (lookup sg' x) })
                            (b:binding)
                            (t:src_ty)
                            (d:src_ty_ok (sg'@sg) t)
  : GTot (d':src_ty_ok (sg'@((x, b)::sg)) t { t_height d' == t_height d })
         (decreases d)
  = match d with
    | OK_TBool _ -> OK_TBool _
    | OK_TArrow _ _ _ d1 d2 -> 
      let d1 = src_ty_ok_weakening _ _ _ _ _ d1 in
      let d2 = src_ty_ok_weakening _ _ _ _ _ d2 in      
      OK_TArrow _ _ _ d1 d2
    | OK_TRefine _ _ d -> OK_TRefine _ _ d

let rec src_ty_ok_renaming (sg:src_env)
                           (x:var { None? (lookup sg x) })
                           (y:var { None? (lookup sg y) })
                           (b:binding)
                           (t:src_ty { ln_ty t })
                           (d:src_ty_ok ((x,b)::sg) t)
  : GTot (d':src_ty_ok ((y,b)::sg) t { t_height d' == t_height d })
         (decreases d)
  = admit()

let rec rename (e:src_exp) (x y:var) 
  : src_exp
  = match e with
    | EBool _ -> e
    | EBVar _ -> e
    | EVar m -> if m = x then EVar y else EVar m
    | EIf b e1 e2 -> EIf (rename b x y) (rename e1 x y) (rename e2 x y)
    | ELam t e -> ELam t (rename e x y)
    | EApp e1 e2 -> EApp (rename e1 x y) (rename e2 x y)


let rec src_typing_renaming (sg sg':src_env)
                            (x:var { None? (lookup sg x) && None? (lookup sg' x)})
                            (y:var { None? (lookup sg y) && None? (lookup sg' y)})
                            (b:binding)
                            (e:src_exp)
                            (t:src_ty)
                            (d:src_typing (sg'@((x,b)::sg)) e t)
  : GTot (d':src_typing (sg'@((y,b)::sg)) (rename e x y) t { height d' == height d })
         (decreases d)
  = match d with
    | T_Bool _ b ->
      T_Bool _ b
      
    | T_Var _ z -> 
       if z = x
       then (
         admit();
         T_Var _ y
       )
       else (
         admit();
         T_Var _ z
       )

    | T_Lam g t body t' z dt dbody ->
//      let dt : src_ty_ok (s(y,b)::) t = src_ty_ok_renaming sg x y b t dt in
      let zz = fresh ((y,b) :: sg) in
      fresh_is_fresh ((y,b) :: sg);
      let dbody
        : src_typing ((z, Inl t)::g) (open_exp body z) t'
        = dbody
      in
      admit()

    | _ -> admit()


let rec src_typing_weakening (sg sg':src_env) 
                             (x:var { None? (lookup sg x) && None? (lookup sg' x) })
                             (b:binding)
                             (e:src_exp { ln e })
                             (t:src_ty)                         
                             (d:src_typing (sg'@sg) e t)
  : GTot (d':src_typing (sg'@((x, b)::sg)) e t { height d == height d' })
         (decreases (height d))
  = admit()
  // match d with
  //   | T_Bool _ b -> T_Bool _ b

  //   | T_Var _ y -> 
  //     assert (lookup (sg'@sg) y == Some (Inl t));
  //     assume (lookup (sg'@((x,b)::sg)) y == Some (Inl t));      
  //     T_Var _ y

  //   | T_Lam g t e t' y dt de ->
  //     assert (None? (lookup (sg'@sg) y));
  //     let dt = src_ty_ok_weakening sg sg' x b _ dt in
  //     let y' = fresh (sg'@((x,b) :: sg)) in
  //     fresh_is_fresh (sg'@((x,b) :: sg));
  //     assume (None? (lookup (sg'@sg) y'));
  //     let de 
  //       : src_typing ((y', Inl t)::(sg'@sg)) (open_exp e y') t'
  //       = src_typing_renaming _ y y' (Inl t) _ _ de
  //     in
  //     assume ((y', Inl t)::(sg'@sg) == ((y', Inl t)::sg')@sg);
  //     assume (None? (lookup ((y', Inl t)::sg') x));
  //     let de
  //       : src_typing (((y',Inl t)::sg') @ (x,b)::sg) (open_exp e y') t'
  //       = src_typing_weakening sg ((y', Inl t)::sg') x b _ _ de 
  //     in
  //     assume ((((y',Inl t)::sg') @ (x,b)::sg) == (y',Inl t)::(sg' @((x,b) ::sg)));
  //     T_Lam (sg' @((x,b) ::sg)) t e t' y' dt de

  //   | T_App g e1 e2 t t' s0 d1 d2 s -> admit()

  //   | T_If _ b e1 e2 t1 t2 t hyp db d1 d2 s1 s2 -> admit()

// let rec src_typing_weakening_alt (sg:src_env)
//                                  (e:src_exp)
//                                  (t:src_ty)
//                                  (d:src_typing [] e t)
//   : GTot (d':src_typing sg e t { height d == height d'})
//   = match d with
//     | T_Bool _ b -> T_Bool _ b
//     | T_Lam _ t e t' x dt ds ->
//       let dt = src_ty_ok_weakening
//     | _ -> admit()
                         
let src_typing_weakening_l (sg:src_env) 
                           (sg':src_env {  //need a stronger refinement here
                                 forall x. Some? (lookup sg' x) ==> None? (lookup sg x)
                           })
                           (e:src_exp)
                           (t:src_ty)                         
                           (d:src_typing sg e t)
  : GTot (d':src_typing L.(sg' @ sg) e t { height d == height d' })
  = admit()

let open_with_fvar_id (fv:R.fv) (x:R.term)
  : Lemma (RT.open_with (R.pack_ln (R.Tv_FVar fv)) x == (R.pack_ln (R.Tv_FVar fv)))
          [SMTPat (RT.open_with (R.pack_ln (R.Tv_FVar fv)) x)]
  = admit()

let subtyping_soundness (#sg:src_env) (#t0 #t1:src_ty) (ds:sub_typing sg t0 t1) (g:fstar_top_env)
  : GTot (RT.sub_typing (extend_env_l g sg) (elab_ty t0) (elab_ty t1))
  = admit()
  
let rec soundness (#sg:src_env) 
                  (#se:src_exp { ln se })
                  (#st:src_ty)
                  (dd:src_typing sg se st)
                  (g:fstar_top_env)
  : GTot (RT.typing (extend_env_l g sg)
                    (elab_exp se)
                    (elab_ty st))
         (decreases (height dd))
  = match dd with
    | T_Bool _ true ->
      RT.T_Const _ _ _ RT.CT_True

    | T_Bool _ false ->
      RT.T_Const _ _ _ RT.CT_False

    | T_Var _ x ->
      RT.T_Var _ (R.pack_bv (RT.make_bv x tun))

    | T_Lam _ t e t' x dt de ->
      let de : RT.typing (extend_env_l g ((x,Inl t)::sg))
                         (elab_exp (open_exp e x))
                         (elab_ty t')
            = soundness de g 
      in    
      let de : RT.typing (RT.extend_env (extend_env_l g sg) x (elab_ty t))
                         (elab_exp (open_exp e x))
                         (elab_ty t')
             = de
      in
      fresh_is_fresh sg;
      let dt : RT.typing (extend_env_l g sg) (elab_ty t) RT.tm_type =
        src_ty_ok_soundness g sg t dt
      in
      let dd
        : RT.typing (extend_env_l g sg)
                    (R.pack_ln (R.Tv_Abs (RT.as_binder 0 (elab_ty t)) (elab_exp e)))
                    (elab_ty (TArrow t t'))
        = RT.T_Abs (extend_env_l g sg)
                   x
                   (elab_ty t) 
                   (elab_exp e)
                   (elab_ty t')
                   dt
                   de
      in
      dd

    | T_App _ e1 e2 t t' t0 d1 d2 st ->
      let dt1 
        : RT.typing (extend_env_l g sg)
                    (elab_exp e1)
                    (elab_ty (TArrow t t'))
        = soundness d1 g
      in
      let dt2
        : RT.typing (extend_env_l g sg)
                    (elab_exp e2)
                    (elab_ty t0)
        = soundness d2 g
      in
      let st
        : RT.sub_typing (extend_env_l g sg) (elab_ty t0) (elab_ty t)
        = subtyping_soundness st g
      in
      let dt2
        : RT.typing (extend_env_l g sg)
                    (elab_exp e2)
                    (elab_ty t)
        = RT.T_Sub _ _ _ _ dt2 st
      in
      RT.T_App _ _ _ _ _ dt1 dt2

    | T_If _ b e1 e2 t1 t2 t hyp db d1 d2 s1 s2 ->
      let db = soundness db g in
      let d1 = soundness d1 g in
      let d2 = soundness d2 g in
      let s1 = subtyping_soundness s1 g in
      let s2 = subtyping_soundness s2 g in
      let d1 = RT.T_Sub _ _ _ _ d1 s1 in
      let d2 = RT.T_Sub _ _ _ _ d2 s2 in      
      RT.T_If (extend_env_l g sg) (elab_exp b) (elab_exp e1) (elab_exp e2) _ hyp db d1 d2


and src_ty_ok_soundness (g:fstar_top_env)
                        (sg:src_env)
                        (t:src_ty { ln_ty t })
                        (dt:src_ty_ok sg t)
 : GTot (RT.typing (extend_env_l g sg) (elab_ty t) RT.tm_type)
        (decreases (t_height dt))
 = match dt with
   | OK_TBool _ ->
     RT.T_FVar _ RT.bool_fv
     
   | OK_TArrow _ t1 t2 ok_t1 ok_t2 ->
     let t1_ok = src_ty_ok_soundness g sg _ ok_t1 in
     let x = fresh sg in
     fresh_is_fresh sg;
     let t2_ok = src_ty_ok_soundness g ((x, Inl t1)::sg) _ (src_ty_ok_weakening _ [] _ _ _ ok_t2) in
     RT.T_Arrow _ x (elab_ty t1) (elab_ty t2) t1_ok t2_ok
     
   | OK_TRefine _ e de ->
     let x = fresh sg in
     fresh_is_fresh sg;
     let sg' = ((fresh sg, Inl TBool)::sg) in
     let de = src_typing_weakening_l [] sg' _ _ de in
     let de : RT.typing (RT.extend_env (extend_env_l g sg) x RT.bool_ty)
                        (elab_exp e)
                        (elab_ty (TArrow TBool TBool)) = soundness de g in
     let arg_x = R.pack_ln (R.Tv_Var (R.pack_bv (RT.make_bv x RT.bool_ty))) in
     let arg_x_typing
       : RT.typing (RT.extend_env (extend_env_l g sg) x RT.bool_ty)
                   arg_x
                   RT.bool_ty
       = RT.T_Var _ (R.pack_bv (RT.make_bv x RT.bool_ty))
     in
     let refinement = R.pack_ln (R.Tv_App (elab_exp e) (arg_x, R.Q_Explicit)) in
     let dr : RT.typing (RT.extend_env (extend_env_l g sg) x RT.bool_ty)
                        refinement
                        RT.bool_ty
            = RT.T_App (RT.extend_env (extend_env_l g sg) x RT.bool_ty)
                       (elab_exp e)
                       (arg_x)
                       (RT.as_binder 0 RT.bool_ty)
                       RT.bool_ty
                       de
                       arg_x_typing
     in
     let dr : RT.typing (RT.extend_env (extend_env_l g sg) x RT.bool_ty)
                        (r_b2t refinement)
                        RT.tm_type
            = b2t_typing _ _ dr
     in
     let arg_bv = R.pack_ln (R.Tv_BVar (R.pack_bv (RT.make_bv 0 RT.bool_ty))) in     
     let refinement' = r_b2t (R.pack_ln (R.Tv_App (elab_exp e) (arg_bv, R.Q_Explicit))) in
     assert (R.pack_ln (R.Tv_Refine (R.pack_bv (RT.make_bv 0 RT.bool_ty)) refinement') ==
             elab_ty t);
     //need a spec for RT.open_term
     assume (RT.open_term refinement' x == r_b2t refinement);
     let bool_typing
       : RT.typing (extend_env_l g sg) RT.bool_ty RT.tm_type 
       = RT.T_FVar _ RT.bool_fv
     in
     RT.T_Refine (extend_env_l g sg) x RT.bool_ty refinement' bool_typing dr

let soundness_lemma (sg:src_env) 
                    (se:src_exp { ln se })
                    (st:src_ty)
                    (g:fstar_top_env)
  : Lemma
    (requires src_typing sg se st)
    (ensures  RT.typing (extend_env_l g sg)
                        (elab_exp se)
                        (elab_ty st))
  = FStar.Squash.bind_squash 
      #(src_typing sg se st)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness dd g))

let main (g:fstar_top_env)
         (src:src_exp)
  : T.Tac (e:R.term & t:R.term { RT.typing g e t })
  = if ln src
    then 
      let (| src', src_ty, _ |) = check g [] src in
      soundness_lemma [] src' src_ty g;
      (| elab_exp src', elab_ty src_ty |)
    else T.fail "Not locally nameless"
