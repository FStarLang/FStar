module DependentBoolRefinement
module T = FStar.Tactics
module R = FStar.Reflection
open FStar.List.Tot
module L = FStar.List.Tot
#push-options "--z3cliopt 'smt.qi.eager_threshold=100' --z3cliopt 'smt.arith.nl=false'"

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
    
let rec freevars (e:src_exp) 
  : FStar.Set.set var
  = match e with
    | EVar v -> Set.singleton v
    | EBool _
    | EBVar _ -> Set.empty
    | EIf b e1 e2 -> Set.union (freevars b) (Set.union (freevars e1) (freevars e2))
    | ELam t e -> Set.union (freevars_ty t) (freevars e)
    | EApp e1 e2 -> Set.union (freevars e1) (freevars e2)
and freevars_ty (t:src_ty)
  : Set.set var
  = match t with
    | TBool -> Set.empty
    | TArrow t1 t2 -> freevars_ty t1 `Set.union` freevars_ty t2
    | TRefineBool e -> freevars e
    
let rec ln' (e:src_exp) (n:int)
  : bool
  = match e with
    | EBool _
    | EVar _ -> true
    | EBVar m -> m <= n
    | EIf b e1 e2 -> ln' b n && ln' e1 n && ln' e2 n
    | ELam t e -> ln_ty' t n && ln' e (n + 1)
    | EApp e1 e2 -> ln' e1 n && ln' e2 n
    
and ln_ty' (t:src_ty) (n:int)
  : bool
  = match t with
    | TBool -> true
    | TRefineBool e -> ln' e (n + 1)
    | TArrow t1 t2 -> ln_ty' t1 n && ln_ty' t2 (n + 1) //Pi types
  
let ln e = ln' e (-1)
let ln_ty t = ln_ty' t (-1)

let rec open_exp' (e:src_exp) (v:src_exp) (n:index)
  : Tot src_exp
        (decreases e)
    = match e with
    | EBool _ -> e
    | EVar m -> EVar m
    | EBVar m -> if m = n then v else EBVar m
    | EIf b e1 e2 -> EIf (open_exp' b v n) (open_exp' e1 v n) (open_exp' e2 v n)
    | ELam t e -> ELam (open_ty' t v n) (open_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (open_exp' e1 v n) (open_exp' e2 v n)
    
and open_ty' (t:src_ty) (v:src_exp) (n:index)
  : Tot src_ty
        (decreases t)
  = match t with
    | TBool -> TBool
    | TRefineBool e -> TRefineBool (open_exp' e v (n + 1))
    | TArrow t1 t2 -> TArrow (open_ty' t1 v n) (open_ty' t2 v (n + 1))

let rec close_exp' (e:src_exp) (v:var) (n:nat)
  : Tot src_exp
        (decreases e)
  = match e with
    | EBool _ -> e
    | EVar m -> if m = v then EBVar n else EVar m
    | EBVar m -> EBVar m
    | EIf b e1 e2 -> EIf (close_exp' b v n) (close_exp' e1 v n) (close_exp' e2 v n)
    | ELam t e -> ELam (close_ty' t v n) (close_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (close_exp' e1 v n) (close_exp' e2 v n)
    
and close_ty' (t:src_ty) (v:var) (n:index)
  : Tot src_ty
        (decreases t)
  = match t with
    | TBool -> TBool
    | TRefineBool e -> TRefineBool (close_exp' e v (n + 1))
    | TArrow t1 t2 -> TArrow (close_ty' t1 v n) (close_ty' t2 v (n + 1))

let open_exp e v = open_exp' e (EVar v) 0
let close_exp e v = close_exp' e v 0
let open_with e e' = open_exp' e e' 0

let open_ty t v = open_ty' t (EVar v) 0
let close_ty t v = close_ty' t v 0
let open_ty_with t e = open_ty' t e 0

#push-options "--query_stats --fuel 4 --ifuel 2 --z3rlimit_factor 8"
let rec open_exp_freevars (e:src_exp) (v:src_exp) (n:nat)
  : Lemma 
    (ensures (freevars e `Set.subset` freevars (open_exp' e v n))  /\
             (freevars (open_exp' e v n) `Set.subset` (freevars e `Set.union` freevars v)))
    (decreases e)
    // [SMTPat (freevars (open_exp' e v n))]
  = match e with
    | EBool _
    | EBVar _ 
    | EVar _ -> ()
    | EApp e1 e2 ->
      open_exp_freevars e1 v n;
      open_exp_freevars e2 v n
    | EIf b e1 e2 ->
      open_exp_freevars b v n;    
      open_exp_freevars e1 v n;
      open_exp_freevars e2 v n
    | ELam t e ->
      open_ty_freevars t v n;
      open_exp_freevars e v (n + 1)

and open_ty_freevars (t:src_ty) (v:src_exp) (n:nat)
  : Lemma 
    (ensures (freevars_ty t `Set.subset` freevars_ty (open_ty' t v n))  /\
             (freevars_ty (open_ty' t v n) `Set.subset` (freevars_ty t `Set.union` freevars v)))
    (decreases t)
    // [SMTPat (freevars_ty (open_ty' t v n))]
  = match t with
    | TBool -> ()
    | TArrow t1 t2 ->
      open_ty_freevars t1 v n;
      open_ty_freevars t2 v (n + 1)
    | TRefineBool e ->
      open_exp_freevars e v (n + 1)
#pop-options

//environment binds types or equations
let src_eqn = src_exp & src_exp
let binding = either src_ty src_eqn
let src_env = list (var & binding)

let rec lookup (e:list (var & 'a)) (x:var)
  : option 'a
  = match e with
    | [] -> None
    | (y, v) :: tl -> if x = y then Some v else lookup tl x

let rec src_env_ok (s:src_env)
  : bool
  = match s with
    | [] -> true
    | (x, _)::tl -> None? (lookup tl x) && src_env_ok tl

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
module RT = Refl.Typing


let b2t_lid : R.name = ["Prims"; "b2t"]
let b2t_fv : R.fv = R.pack_fv b2t_lid
let b2t_ty : R.term = R.(pack_ln (Tv_Arrow (RT.as_binder 0 RT.bool_ty) (RT.mk_total (RT.tm_type RT.u_zero))))
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
          (RT.mk_total t2)) //(R.pack_comp (C_Total t2 [])))
          
    | TRefineBool e ->
      let e = elab_exp e in
      let bv = R.pack_bv (RT.make_bv 0 RT.bool_ty) in
      let refinement = r_b2t e in
      R.pack_ln (Tv_Refine bv refinement)

let elab_eqn (e1 e2:src_exp)
  : R.term
  = RT.eq2 RT.bool_ty (elab_exp e1) (elab_exp e2)

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

let fstar_env =
  g:R.env { 
    RT.lookup_fvar g RT.bool_fv == Some (RT.tm_type RT.u_zero) /\
    RT.lookup_fvar g b2t_fv == Some b2t_ty
  }

let fstar_top_env =
  g:fstar_env { 
    forall x. None? (RT.lookup_bvar g x )
  }

[@@erasable]
noeq
type sub_typing (f:fstar_top_env) : src_env -> src_ty -> src_ty -> Type =
  | S_Refl : g:src_env -> t:src_ty -> sub_typing f g t t
  | S_ELab : g:src_env -> t0:src_ty -> t1:src_ty ->
             RT.sub_typing (extend_env_l f g) (elab_ty t0) (elab_ty t1) ->
             sub_typing f g t0 t1

  
[@@erasable]
noeq
type src_typing (f:fstar_top_env) : src_env -> src_exp -> src_ty -> Type =
  | T_Bool :
      g:src_env ->
      b:bool ->
      src_typing f g (EBool b) TBool
  
  | T_Var  :
      g:src_env ->
      x:var { Some? (lookup_ty g x) } ->
      src_typing f g (EVar x) (Some?.v (lookup_ty g x))

  | T_Lam  :
      g:src_env ->
      t:src_ty ->
      e:src_exp ->
      t':src_ty ->
      x:var { None? (lookup g x) /\ ~ (x `Set.mem` freevars e)} ->
      src_ty_ok f g t ->
      src_typing f ((x, Inl t) :: g) (open_exp e x) t' ->
      src_typing f g (ELam t e) (TArrow t (close_ty t' x))

  | T_App  :
      g:src_env ->
      e1:src_exp ->
      e2:src_exp ->
      t:src_ty ->
      t':src_ty ->
      t0:src_ty ->
      src_typing f g e1 (TArrow t t') ->
      src_typing f g e2 t0 ->
      sub_typing f g t0 t ->
      src_typing f g (EApp e1 e2) (open_ty_with t' e2)

   | T_If :
       g:src_env ->
       b:src_exp ->
       e1:src_exp ->
       e2:src_exp ->
       t1:src_ty ->
       t2:src_ty ->
       t:src_ty ->
       hyp:var { None? (lookup g hyp) /\ ~ (hyp `Set.mem` freevars e1) /\ ~ (hyp `Set.mem` freevars e2) } ->
       src_typing f g b TBool ->
       src_typing f ((hyp, Inr (b, EBool true)) :: g) e1 t1 ->
       src_typing f ((hyp, Inr (b, EBool false)) :: g) e2 t2 ->
       sub_typing f ((hyp, Inr (b, EBool true)) :: g) t1 t ->
       sub_typing f ((hyp, Inr (b, EBool false)) :: g) t2 t ->
       src_typing f g (EIf b e1 e2) t
       
and src_ty_ok (f:fstar_top_env) : src_env -> src_ty -> Type =
  | OK_TBool  : g:src_env -> src_ty_ok f g TBool
  | OK_TArrow :
      g:src_env ->
      t:src_ty ->
      t':src_ty ->
      x:var { None? (lookup g x) /\ ~ (x `Set.mem` freevars_ty t')} ->
      src_ty_ok f g t ->
      src_ty_ok f ((x,Inl t)::g) (open_ty t' x) ->
      src_ty_ok f g (TArrow t t')
      
  | OK_TRefine:
      g:src_env ->
      e:src_exp ->
      x:var { None? (lookup g x) /\ ~ (x `Set.mem` freevars e)} ->
      src_typing f ((x, Inl TBool)::g) (open_exp e x) TBool ->
      src_ty_ok f g (TRefineBool e)

let s_height #f #g #t0 #t1 (d:sub_typing f g t0 t1)
  : GTot nat
  = 1
  
let rec height #f #g #e #t (d:src_typing f g e t)
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
    
and t_height #f (#g:src_env) (#t:src_ty) (d:src_ty_ok f g t)    
  : GTot nat (decreases d)
  = match d with
    | OK_TBool _ -> 1
    | OK_TArrow _ _ _ _ d0 d1 -> max (t_height d0) (t_height d1) + 1
    | OK_TRefine _ _ _ d -> height d + 1

let check_sub_typing f
                     (sg:src_env)
                     (t0 t1:src_ty)
  : T.Tac (sub_typing f sg t0 t1)
  = if t0 = t1 then S_Refl _ t0
    else T.fail "Not subtypes"

let weaken (f:fstar_top_env) (sg:src_env) (hyp:var { None? (lookup sg hyp) } ) (b:src_exp) (t0 t1:src_ty)
  : T.Tac (t:src_ty &
           sub_typing f ((hyp,Inr(b, EBool true))::sg) t0 t &
           sub_typing f ((hyp,Inr(b, EBool false))::sg) t1 t)
  = if t0 = t1
    then (| t0, S_Refl _ t0, S_Refl _ t1 |)
    else T.fail "weaken is very dumb"

let ok (sg:src_env) (e:src_exp) = (forall x. x `Set.mem` freevars e ==> Some? (lookup sg x))
let ok_ty (sg:src_env) (e:src_ty) = (forall x. x `Set.mem` freevars_ty e ==> Some? (lookup sg x))

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 6 --query_stats"

let rec check (f:fstar_top_env)
              (sg:src_env)
              (e:src_exp { ok sg e })
  : T.Tac (t:src_ty &
           src_typing f sg e t)
  = match e with
    | EBVar _ ->
      T.fail "Not locally nameless"
    
    | EBool b ->
      (| TBool, T_Bool _ b |)

    | EVar n ->
      begin
      match lookup_ty sg n with
      | None -> T.fail "Ill-typed"
      | Some t ->
        let d = T_Var sg n in
        (| t, d |)
      end

    
    | ELam t body -> 
      let t_ok = check_ty f sg t in
      let x = fresh sg in
      fresh_is_fresh sg;
      open_exp_freevars body (EVar x) 0;
      let (| tbody, dbody |) = check f ((x, Inl t)::sg) (open_exp body x) in
      let dd : src_typing f sg e (TArrow t (close_ty tbody x)) = 
             T_Lam sg t body tbody x t_ok dbody in
      (| TArrow t (close_ty tbody x), dd |)


    | EApp e1 e2 ->
      let (| t1, d1 |) = check f sg e1  in
      let (| t2, d2 |) = check f sg e2 in
      begin
      match t1 with
      | TArrow t_arg t_res ->
        let st_ok = check_sub_typing f sg t2 t_arg in
        (| open_ty_with t_res e2, T_App _ _ _ t_arg t_res _ d1 d2 st_ok |)

      | _ -> 
        T.fail "Expected a function"
      end

    
    | EIf b e1 e2 ->
      let (| tb, ok_b |) = check f sg b in
      let hyp = fresh sg in
      fresh_is_fresh sg;
      if tb = TBool
      then (
        let (| t1, ok_1 |) = check f ((hyp, Inr(b, EBool true))::sg) e1 in
        let (| t2, ok_2 |) = check f ((hyp, Inr(b, EBool false))::sg) e2 in      
        let (| t, w1, w2 |) = weaken f sg hyp b t1 t2 in
        (| t, T_If _ _ _ _ _ _ _ hyp ok_b ok_1 ok_2 w1 w2 |)
      )
      else T.fail "Branching on a non-boolean"

and check_ty (f:fstar_top_env)
             (sg:src_env)
             (t:src_ty { ok_ty sg t })
  : T.Tac (src_ty_ok f sg t)
  = match t with
    | TBool -> OK_TBool _ 


    | TArrow t t' ->
      let t_ok = check_ty f sg t in
      let x = fresh sg in
      fresh_is_fresh sg;
      open_ty_freevars t' (EVar x) 0;
      let t'_ok = check_ty f ((x, Inl t)::sg) (open_ty t' x) in      
      OK_TArrow _ _ _ x t_ok t'_ok

    | TRefineBool e ->
      let x = fresh sg in
      fresh_is_fresh sg;
      open_exp_freevars e (EVar x) 0;      
      let (| te, de |) = check f ((x, Inl TBool)::sg) (open_exp e x) in
      match te with 
      | TBool -> OK_TRefine sg e x de
      | _ -> T.fail "Ill-typed refinement"
#pop-options
  
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

#push-options "--query_stats --fuel 8 --ifuel 2 --z3rlimit_factor 2"
let rec elab_open_commute' (n:nat) (e:src_exp) (x:src_exp) 
  : Lemma (ensures
              RT.open_or_close_term' (elab_exp e) (RT.OpenWith (elab_exp x)) n ==
              elab_exp (open_exp' e x n))
          (decreases e)
  = match e with
    | EBool _ -> ()
    | EBVar _ -> ()
    | EVar _ -> ()
    | EApp e1 e2 -> 
      elab_open_commute' n e1 x;
      elab_open_commute' n e2 x
    | EIf b e1 e2 ->
      elab_open_commute' n b x;    
      elab_open_commute' n e1 x;
      elab_open_commute' n e2 x
    | ELam t e ->
      elab_ty_open_commute' n t x;
      elab_open_commute' (n + 1) e x

and elab_ty_open_commute' (n:nat) (e:src_ty) (x:src_exp)
  : Lemma
    (ensures
      RT.open_or_close_term' (elab_ty e) (RT.OpenWith (elab_exp x)) n ==
      elab_ty (open_ty' e x n))
    (decreases e)
  = match e with
    | TBool -> ()
    | TArrow t t' ->
      elab_ty_open_commute' n t x;
      elab_ty_open_commute' (n + 1) t' x

    | TRefineBool e ->
      elab_open_commute' (n + 1) e x
#pop-options

let elab_open_commute (e:src_exp) (x:var)
  : Lemma (RT.open_term (elab_exp e) x == elab_exp (open_exp e x))
          [SMTPat (RT.open_term (elab_exp e) x)]
  = elab_open_commute' 0 e (EVar x);
    RT.open_term_spec (elab_exp e) x
    
let b2t_typing (g:fstar_env) (t:R.term) (dt:RT.typing g t RT.bool_ty)
  : RT.typing g (r_b2t t) (RT.tm_type RT.u_zero)
  = let b2t_typing : RT.typing g _ b2t_ty = RT.T_FVar g b2t_fv in
    let app_ty : _ = RT.T_App _ _ _ _ _ b2t_typing dt in
    RT.open_with_spec (RT.tm_type RT.u_zero) t;
    app_ty

let rec extend_env_l_lookup_fvar (g:R.env) (sg:src_env) (fv:R.fv)
  : Lemma 
    (ensures
      RT.lookup_fvar (extend_env_l g sg) fv ==
      RT.lookup_fvar g fv)
    [SMTPat (RT.lookup_fvar (extend_env_l g sg) fv)]
  = match sg with
    | [] -> ()
    | hd::tl -> extend_env_l_lookup_fvar g tl fv

#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 2"

let subtyping_soundness #f (#sg:src_env) (#t0 #t1:src_ty) (ds:sub_typing f sg t0 t1)
  : GTot (RT.sub_typing (extend_env_l f sg) (elab_ty t0) (elab_ty t1))
  = match ds with
    | S_Refl _ _ -> RT.ST_Equiv _ _ _ (RT.EQ_Refl _ _)
    | S_ELab _ _ _ d -> d

#push-options "--query_stats --fuel 8 --ifuel 2 --z3rlimit_factor 2"
let rec elab_close_commute' (n:nat) (e:src_exp) (x:var)
  : Lemma (ensures
              RT.open_or_close_term' (elab_exp e) (RT.CloseVar x) n ==
              elab_exp (close_exp' e x n))
          (decreases e)
  = match e with
    | EBool _ -> ()
    | EBVar _ -> ()
    | EVar _ -> ()
    | EApp e1 e2 -> 
      elab_close_commute' n e1 x;
      elab_close_commute' n e2 x
    | EIf b e1 e2 ->
      elab_close_commute' n b x;    
      elab_close_commute' n e1 x;
      elab_close_commute' n e2 x
    | ELam t e ->
      elab_ty_close_commute' n t x;
      elab_close_commute' (n + 1) e x

and elab_ty_close_commute' (n:nat) (e:src_ty) (x:var)
  : Lemma
    (ensures
      RT.open_or_close_term' (elab_ty e) (RT.CloseVar x) n ==
      elab_ty (close_ty' e x n))
    (decreases e)
  = match e with
    | TBool -> ()
    | TArrow t t' ->
      elab_ty_close_commute' n t x;
      elab_ty_close_commute' (n + 1) t' x

    | TRefineBool e ->
      elab_close_commute' (n + 1) e x
#pop-options

let elab_ty_close_commute (e:src_ty) (x:var)
  : Lemma (RT.close_term (elab_ty e) x == elab_ty (close_ty e x))
          [SMTPat (RT.close_term (elab_ty e) x)]
  = RT.close_term_spec (elab_ty e) x;
    elab_ty_close_commute' 0 e x
    
let elab_ty_open_with_commute (e:src_ty) (v:src_exp)
  : Lemma (RT.open_with (elab_ty e) (elab_exp v) == elab_ty (open_ty_with e v))
          [SMTPat (RT.open_with (elab_ty e) (elab_exp v))]
  = elab_ty_open_commute' 0 e v;
    RT.open_with_spec (elab_ty e) (elab_exp v)

let elab_ty_open_commute (e:src_ty) (v:var)
  : Lemma (RT.open_term (elab_ty e) v == elab_ty (open_ty e v))
          [SMTPat (RT.open_term (elab_ty e) v)]
  = elab_ty_open_commute' 0 e (EVar v);
    RT.open_term_spec (elab_ty e) v

let elab_open_b2t (e:src_exp) (x:var) 
  : Lemma (RT.open_term (r_b2t (elab_exp e)) x ==
           r_b2t (elab_exp (open_exp e x)))
  = RT.open_term_spec (r_b2t (elab_exp e)) x;
    RT.open_term_spec (elab_exp e) x

let rec soundness (#f:fstar_top_env)
                  (#sg:src_env { src_env_ok sg } ) 
                  (#se:src_exp)
                  (#st:src_ty)
                  (dd:src_typing f sg se st)
  : GTot (RT.typing (extend_env_l f sg)
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
      let de : RT.typing (extend_env_l f ((x,Inl t)::sg))
                         (elab_exp (open_exp e x))
                         (elab_ty t')
            = soundness de
      in    
      let de : RT.typing (RT.extend_env (extend_env_l f sg) x (elab_ty t))
                         (elab_exp (open_exp e x))
                         (elab_ty t')
             = de
      in
      fresh_is_fresh sg;
      let dt : RT.typing (extend_env_l f sg) (elab_ty t) (RT.tm_type RT.u_zero) =
        src_ty_ok_soundness sg t dt
      in
      let dd
        : RT.typing (extend_env_l f sg)
                    (R.pack_ln (R.Tv_Abs (RT.as_binder 0 (elab_ty t)) (elab_exp e)))
                    (elab_ty (TArrow t (close_ty t' x)))
        = RT.T_Abs (extend_env_l f sg)
                   x
                   (elab_ty t) 
                   (elab_exp e)
                   (elab_ty t')
                   _
                   _
                   _
                   dt
                   de
      in
      dd

    | T_If _ b e1 e2 t1 t2 t hyp db d1 d2 s1 s2 ->
      let db = soundness db in
      let d1 = soundness d1 in
      let d2 = soundness d2 in
      let s1 = subtyping_soundness s1 in
      let s2 = subtyping_soundness s2 in
      let d1 = RT.T_Sub _ _ _ _ d1 s1 in
      let d2 = RT.T_Sub _ _ _ _ d2 s2 in      
      RT.T_If (extend_env_l f sg) (elab_exp b) (elab_exp e1) (elab_exp e2) _ hyp db d1 d2

    | T_App _ e1 e2 t t' t0 d1 d2 st ->
      let dt1 
        : RT.typing (extend_env_l f sg)
                    (elab_exp e1)
                    (elab_ty (TArrow t t'))
        = soundness d1
      in
      let dt2
        : RT.typing (extend_env_l f sg)
                    (elab_exp e2)
                    (elab_ty t0)
        = soundness d2
      in
      let st
        : RT.sub_typing (extend_env_l f sg) (elab_ty t0) (elab_ty t)
        = subtyping_soundness st
      in
      let dt2
        : RT.typing (extend_env_l f sg)
                    (elab_exp e2)
                    (elab_ty t)
        = RT.T_Sub _ _ _ _ dt2 st
      in
      RT.T_App _ _ _ _ _ dt1 dt2

and src_ty_ok_soundness (#f:fstar_top_env)
                        (sg:src_env { src_env_ok sg })
                        (t:src_ty)
                        (dt:src_ty_ok f sg t)
 : GTot (RT.typing (extend_env_l f sg) (elab_ty t) (RT.tm_type RT.u_zero))
        (decreases (t_height dt))
 = match dt with
   | OK_TBool _ ->
     RT.T_FVar _ RT.bool_fv

   | OK_TArrow _ t1 t2 x ok_t1 ok_t2 ->
     let t1_ok = src_ty_ok_soundness sg _ ok_t1 in
     let t2_ok = src_ty_ok_soundness ((x, Inl t1)::sg) _ ok_t2 in
     let arr_max = RT.T_Arrow _ x (elab_ty t1) (elab_ty t2) _ _ "x" R.Q_Explicit t1_ok t2_ok in
     RT.simplify_umax arr_max

   | OK_TRefine _ e x de ->
     let de 
       : RT.typing (RT.extend_env (extend_env_l f sg) x RT.bool_ty)
                   (elab_exp (open_exp e x))
                   (elab_ty TBool)
       = soundness de
     in
     let de
       : RT.typing (RT.extend_env (extend_env_l f sg) x RT.bool_ty)
                   (r_b2t (elab_exp (open_exp e x)))
                   (RT.tm_type RT.u_zero)
       = b2t_typing _ _ de
     in
     let bool_typing
       : RT.typing (extend_env_l f sg) RT.bool_ty (RT.tm_type RT.u_zero)
       = RT.T_FVar _ RT.bool_fv
     in
     elab_open_b2t e x;
     RT.T_Refine (extend_env_l f sg)
                 x
                 RT.bool_ty
                 (r_b2t (elab_exp e))
                 _ _
                 bool_typing 
                 de

let soundness_lemma (f:fstar_top_env)
                    (sg:src_env { src_env_ok sg }) 
                    (se:src_exp)
                    (st:src_ty)
  : Lemma
    (requires src_typing f sg se st)
    (ensures  RT.typing (extend_env_l f sg)
                        (elab_exp se)
                        (elab_ty st))
  = FStar.Squash.bind_squash 
      #(src_typing f sg se st)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness dd))

let rec closed (s:src_exp) 
  : b:bool { b <==> (freevars s `Set.equal` Set.empty) }
  = match s with
    | EBool _
    | EBVar _ -> true
    | EVar m -> assert (m `Set.mem` freevars s); false
    | EIf b e1 e2 -> closed b && closed e1 && closed e2
    | ELam t e -> closed_ty t && closed e
    | EApp e1 e2 -> closed e1 && closed e2

and closed_ty (t:src_ty)
  : b:bool { b <==> (freevars_ty t `Set.equal` Set.empty) }
  = match t with
    | TBool -> true
    | TRefineBool e -> closed e
    | TArrow t1 t2 -> closed_ty t1 && closed_ty t2

let main (f:fstar_top_env)
         (src:src_exp)
  : T.Tac (e:R.term & t:R.term { RT.typing f e t })
  = if closed src
    then 
      let (| src_ty, _ |) = check f [] src in
      soundness_lemma f [] src src_ty;
      (| elab_exp src, elab_ty src_ty |)
    else T.fail "Not locally nameless"
