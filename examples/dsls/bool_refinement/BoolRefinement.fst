module STLC
module T = FStar.Tactics
module R = FStar.Reflection
module L = FStar.List.Tot


let var = nat
let index = nat

let tun = R.pack_ln R.Tv_Unknown

noeq
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
    | ELam _ e -> ln' e (n + 1)
    | EApp e1 e2 -> ln' e1 n && ln' e2 n

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


let src_env = list (either (var & src_ty)      //either a type binding
                           (src_exp & src_exp) //or an equation between two src exps
                           )

let rec lookup (e:src_env) (x:var)
  : option src_ty
  = match e with
    | [] -> None
    | Inl (y, t) :: tl -> if x = y then Some t else lookup tl x
    | Inr _ :: tl -> lookup tl x

let max (n1 n2:nat) = if n1 < n2 then n2 else n1

let rec fresh (e:src_env)
  : var
  = match e with
    | [] -> 0
    | Inl (y, _) :: tl ->  max (fresh tl) y + 1
    | _ :: tl -> fresh tl

// let rec fresh_not_mem (e:list (var & 'a)) (elt: (var & 'a))
//   : Lemma (ensures L.memP elt e ==> fresh e > fst elt)
//   = match e with
//     | [] -> ()
//     | hd :: tl -> fresh_not_mem tl elt
  
// let rec lookup_mem (e:list (var & 'a)) (x:var)
//   : Lemma
//     (requires Some? (lookup e x))
//     (ensures exists elt. L.memP elt e /\ fst elt == x)
//   = match e with
//     | [] -> ()
//     | hd :: tl -> 
//       match lookup tl x with
//       | None -> assert (L.memP hd e)
//       | _ -> 
//         lookup_mem tl x;
//         eliminate exists elt. L.memP elt tl /\ fst elt == x
//         returns _
//         with _ . ( 
//           introduce exists elt. L.memP elt e /\ fst elt == x
//           with elt
//           and ()
//         )

let fresh_is_fresh (e:src_env)
  : Lemma (None? (lookup e (fresh e)))
  = admit()

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
      x:var { Some? (lookup g x) } ->
      src_typing g (EVar x) (Some?.v (lookup g x))

  | T_Lam  :
      g:src_env ->
      t:src_ty ->
      e:src_exp ->
      t':src_ty ->
      x:var { x == fresh g } ->
      src_ty_ok g t ->
      src_typing (Inl(x,t)::g) (open_exp e x) t' ->
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
       src_typing (Inr (b, EBool true) :: g) e1 t1 ->
       src_typing (Inr (b, EBool false) :: g) e2 t2 ->
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
      match lookup sg n with
      | None -> T.fail "Ill-typed"
      | Some t ->
        let d = T_Var sg n in
        (| EVar n, t, d |)
      end

    | _ -> admit()
    | ELam t e ->
      let x = fresh sg in
      fresh_is_fresh sg;
      let t = read_back g rt in
      let (| e, tbody, dbody |) = check g ((x,t)::sg) (open_exp e x) in
      (| ELam t (close_exp e x), 
         TArrow t tbody, 
         T_Lam sg t (close_exp e x) tbody x dbody |)
           
    | EApp e1 e2 ->
      let (| e1, t1, d1 |) = check g sg e1  in
      let (| e2, t2, d2 |) = check g sg e2 in
      match t1 with
      | TArrow t2' t ->
        if t2' = t2
        then (| EApp e1 e2, t, T_App _ _ _ _ _ d1 d2 |)
        else T.fail "Inference went wrong"
        
      | _ -> 
        T.fail "Inference went wrong"

let infer_and_check (g:R.env)
                    (e:stlc_exp unit { ln e })
  : T.Tac (e':s_exp { ln e' } &
           t :stlc_ty { stlc_typing [] e' t })
  = let (| e', _ |) = infer g [] e in
    let (| e'', t', d |) = check g [] e' in
    (| e'', t' |)

module RT = Refl.Typing

let rec elab_ty (t:stlc_ty) 
  : R.term 
  = let open R in
    match t with
    | TUnit -> 
      R.pack_ln (R.Tv_FVar (R.pack_fv unit_lid))
      
    | TArrow t1 t2 ->
      let t1 = elab_ty t1 in
      let t2 = elab_ty t2 in

      R.pack_ln 
        (R.Tv_Arrow 
          (RT.as_binder 0 t1)
          (R.pack_comp (C_Total t2 [])))
  
let rec elab_exp (e:s_exp)
  : Tot R.term (decreases (size e))
  = let open R in
    match e with
    | EUnit -> 
      pack_ln (Tv_Const C_Unit)

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

let extend_env_l (g:R.env) (sg:stlc_env) = 
  L.fold_right (fun (x, t) g -> RT.extend_env g x (elab_ty t)) sg g
  
let rec extend_env_l_lookup_bvar (g:R.env) (sg:stlc_env) (x:var)
  : Lemma 
    (requires (forall x. RT.lookup_bvar g x == None))
    (ensures (
      match lookup sg x with
      | Some t -> RT.lookup_bvar (extend_env_l g sg) x == Some (elab_ty t)
      | None -> RT.lookup_bvar (extend_env_l g sg) x == None))
    (decreases sg)
    [SMTPat (RT.lookup_bvar (extend_env_l g sg) x)]
  = match sg with
    | [] -> ()
    | hd :: tl -> extend_env_l_lookup_bvar g tl x

let elab_open_commute (e:s_exp) (x:var)
  : Lemma (RT.open_term (elab_exp e) x == elab_exp (open_exp e x))
          [SMTPat (RT.open_term (elab_exp e) x)]
  = admit()

//key lemma about STLC types
let stlc_types_are_closed1 (ty:stlc_ty) (v:R.term)
  : Lemma (RT.open_with (elab_ty ty) v == elab_ty ty)
          [SMTPat (RT.open_with (elab_ty ty) v)]
  = admit()

let stlc_types_are_closed2 (ty:stlc_ty) (x:R.var)
  : Lemma (RT.close_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.close_term (elab_ty ty) x)]
  = admit()

let rec soundness (#sg:stlc_env) 
                  (#se:s_exp)
                  (#st:stlc_ty)
                  (dd:stlc_typing sg se st)
                  (g:R.env { forall x. None? (RT.lookup_bvar g x) } )
  : GTot (RT.typing (extend_env_l g sg)
                    (elab_exp se)
                    (elab_ty st))
         (decreases dd)
  = match dd with
    | T_Unit _ ->
      RT.T_Const _

    | T_Var _ x ->
      RT.T_Var _ (R.pack_bv (RT.make_bv x tun))

    | T_Lam _ t e t' x de ->
      let de : RT.typing (extend_env_l g ((x,t)::sg))
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
      let dd
        : RT.typing (extend_env_l g sg)
                    (R.pack_ln (R.Tv_Abs (RT.as_binder 0 (elab_ty t)) (elab_exp e)))
                    (elab_ty (TArrow t t'))
        = RT.T_Abs (extend_env_l g sg)
                   x
                   (elab_ty t) 
                   (elab_exp e)
                   (elab_ty t')
                   de
      in
      dd

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
