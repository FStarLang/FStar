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
      x:var { x == fresh g } ->
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
       src_typing g b TBool ->
       src_typing ((fresh g, Inr (b, EBool true)) :: g) e1 t1 ->
       src_typing ((fresh g, Inr (b, EBool false)) :: g) e2 t2 ->
       sub_typing g t1 t ->
       sub_typing g t2 t ->
       src_typing g (EIf b e1 e2) t
       
and src_ty_ok : src_env -> src_ty -> Type =
  | OK_TBool  : g:src_env -> src_ty_ok g TBool
  | OK_TArrow : g:src_env -> t:src_ty -> t':src_ty ->
                src_ty_ok g t ->
                src_ty_ok g t' ->                
                src_ty_ok g (TArrow t t')
  | OK_Refine : g:src_env ->
                e:src_exp ->
                src_typing [] e (TArrow TBool TBool) ->
                src_ty_ok g (TRefineBool e)

let check_sub_typing (g:R.env) 
                     (sg:src_env)
                     (t0 t1:src_ty)
  : T.Tac (sub_typing sg t0 t1)
  = if t0 = t1 then S_Refl _ t0
    else T.fail "Not subtypes"

let weaken (g:R.env) (sg:src_env) (t0 t1:src_ty)
  : T.Tac (t:src_ty & sub_typing sg t0 t & sub_typing sg t1 t)
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
      if tb = TBool
      then (
        let (| e1, t1, ok_1 |) = check g ((hyp, Inr(b, EBool true))::sg) e1 in
        let (| e2, t2, ok_2 |) = check g ((hyp, Inr(b, EBool false))::sg) e2 in      
        let (| t, w1, w2 |) = weaken g sg t1 t2 in
        (| EIf b e1 e2, t, T_If _ _ _ _ _ _ _ ok_b ok_1 ok_2 w1 w2 |)
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
      | TArrow TBool TBool -> (| TRefineBool e, OK_Refine _ _ de |)
      | _ -> T.fail "Ill-typed refinement"
  

module RT = Refl.Typing

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
      let refinement = R.pack_ln (Tv_App e (R.pack_ln (Tv_BVar bv), Q_Explicit)) in
      R.pack_ln (Tv_Refine bv refinement)

module F = FStar.Reflection.Formula
let elab_eqn (e1 e2:src_exp)
  : R.term
  =  F.formula_as_term (F.Comp (F.Eq (Some RT.bool_ty))
                                     (elab_exp e1)
                                     (elab_exp e2))

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
//          [SMTPat (RT.open_with (elab_ty ty) v)]
  = admit()

let src_types_are_closed2 (ty:src_ty) (x:R.var)
  : Lemma (RT.close_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.close_term (elab_ty ty) x)]
  = admit()


let stlc_types_are_closed3 (ty:src_ty) (x:R.var)
  : Lemma (RT.open_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.open_term (elab_ty ty) x)]
  = admit()

let fstar_env =
  g:R.env { 
    RT.lookup_fvar g RT.bool_fv == Some RT.tm_type
  }

let fstar_top_env =
  g:fstar_env { 
    forall x. None? (RT.lookup_bvar g x )
  }

let extend_env_l_lookup_fvar (g:R.env) (sg:src_env) (fv:R.fv)
  : Lemma 
    (ensures
      RT.lookup_fvar (extend_env_l g sg) fv ==
      RT.lookup_fvar g fv)
    [SMTPat (RT.lookup_fvar (extend_env_l g sg) fv)]
  = admit()

let src_ty_ok_weakening (sg:src_env) 
                        (x:var { None? (lookup sg x) })
                        (b:binding)
                        (t:src_ty)
                        (d:src_ty_ok sg t)
  : GTot (src_ty_ok ((x, b)::sg) t)
  = admit()
                        
let rec soundness (#sg:src_env) 
                  (#se:src_exp)
                  (#st:src_ty)
                  (dd:src_typing sg se st)
                  (g:fstar_top_env)
  : GTot (RT.typing (extend_env_l g sg)
                    (elab_exp se)
                    (elab_ty st))
         (decreases dd)
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

    | _ -> admit()

and src_ty_ok_soundness (g:fstar_top_env)
                        (sg:src_env)
                        (t:src_ty)
                        (dt:src_ty_ok sg t)
 : GTot (RT.typing (extend_env_l g sg) (elab_ty t) RT.tm_type)
        (decreases t)
 = match dt with
   | OK_TBool _ -> RT.T_FVar _ RT.bool_fv
   | OK_TArrow _ t1 t2 ok_t1 ok_t2 ->
     let t1_ok = src_ty_ok_soundness g sg _ ok_t1 in
     let x = fresh sg in
     fresh_is_fresh sg;
     let t2_ok = src_ty_ok_soundness g ((x, Inl t1)::sg) _ (src_ty_ok_weakening _ _ _ _ ok_t2) in
     RT.T_Arrow _ x (elab_ty t1) (elab_ty t2) t1_ok t2_ok
     
   | _ -> admit()



    | T_App _ e1 e2 t t' d1 d2 ->
      let dt1 
        : RT.typing (extend_env_l g sg)
                    (elab_exp e1)
                    (elab_ty (TArrow t t'))
        = soundness d1 g
      in
      let dt2
        : RT.typing (extend_env_l g sg)
                    (elab_exp e2)
                    (elab_ty t)
        = soundness d2 g
      in
      let dt :
        RT.typing (extend_env_l g sg)
                  (elab_exp (EApp e1 e2))
                  (RT.open_with (elab_ty t') (elab_exp e2))
        = RT.T_App _ _ _ _ _ dt1 dt2
      in
      dt

let soundness_lemma (sg:stlc_env) 
                    (se:s_exp)
                    (st:stlc_ty)
                    (g:R.env { forall x. None? (RT.lookup_bvar g x ) })                   
  : Lemma
    (requires stlc_typing sg se st)
    (ensures  RT.typing (extend_env_l g sg)
                        (elab_exp se)
                        (elab_ty st))
  = FStar.Squash.bind_squash 
      #(stlc_typing sg se st)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness dd g))

let main (g:R.env { forall x. None? (RT.lookup_bvar g x ) })
         (src:stlc_exp unit)
  : T.Tac (e:R.term & t:R.term { RT.typing g e t })
  = if ln src
    then 
      let (| src', src_ty |) = infer_and_check g src in
      soundness_lemma [] src' src_ty g;
      (| elab_exp src', elab_ty src_ty |)
    else T.fail "Not locally nameless"
