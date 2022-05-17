module STLC
module T = FStar.Tactics
module R = FStar.Reflection
module L = FStar.List.Tot
module RT = Refl.Typing

type stlc_ty =
  | TUnit
  | TArrow : stlc_ty -> stlc_ty -> stlc_ty

let var = nat
let index = nat

let tun = R.pack_ln R.Tv_Unknown

noeq
type stlc_exp (t:Type) =
  | EUnit : stlc_exp t
  | EBVar : index -> stlc_exp t
  | EVar  : var -> stlc_exp t
  | ELam  : t -> stlc_exp t -> stlc_exp t
  | EApp  : stlc_exp t -> stlc_exp t -> stlc_exp t

let rec size (e:stlc_exp 'a) 
  : nat
  = match e with
    | EUnit
    | EBVar _ 
    | EVar _ -> 1
    | ELam _ e -> 1 + size e
    | EApp e1 e2 -> 1 + size e1 + size e2

let rec ln' (e:stlc_exp 'a) (n:int)
  : bool
  = match e with
    | EUnit
    | EVar _ -> true
    | EBVar m -> m <= n
    | ELam _ e -> ln' e (n + 1)
    | EApp e1 e2 -> ln' e1 n && ln' e2 n

let ln e = ln' e (-1)

let rec open_exp' (e:stlc_exp 'a) (v:var) (n:index)
  : e':stlc_exp 'a { size e == size e'}
  = match e with
    | EUnit -> EUnit
    | EVar m -> EVar m
    | EBVar m -> if m = n then EVar v else EBVar m
    | ELam t e -> ELam t (open_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (open_exp' e1 v n) (open_exp' e2 v n)

let rec close_exp' (e:stlc_exp 'a) (v:var) (n:nat)
  : e':stlc_exp 'a { size e == size e'}
  = match e with
    | EUnit -> EUnit
    | EVar m -> if m = v then EBVar n else EVar m
    | EBVar m -> EBVar m
    | ELam t e -> ELam t (close_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (close_exp' e1 v n) (close_exp' e2 v n)

let open_exp e v = open_exp' e v 0
let close_exp e v = close_exp' e v 0

let rec open_close' (e:stlc_exp 'a) (x:var) (n:nat { ln' e (n - 1) })
  : Lemma (open_exp' (close_exp' e x n) x n == e)
  = match e with
    | EUnit -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | ELam _ e -> open_close' e x (n + 1)
    | EApp e1 e2 -> 
      open_close' e1 x n; 
      open_close' e2 x n

let open_close (e:stlc_exp 'a) (x:var)
  : Lemma 
    (requires ln e)
    (ensures open_exp (close_exp e x) x == e)
    [SMTPat (open_exp (close_exp e x) x)]
  = open_close' e x 0

let rec open_exp_ln (e:stlc_exp 'a) (v:var) (n:index) (m:int)
  : Lemma 
    (requires ln' e n /\
              m == n - 1)
    (ensures ln' (open_exp' e v n) m)
    [SMTPat (ln' e n);
     SMTPat (ln' (open_exp' e v n) m)]
  = match e with
    | EUnit -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | ELam _ e -> open_exp_ln e v (n + 1) (m + 1)
    | EApp e1 e2 -> open_exp_ln e1 v n m; open_exp_ln e2 v n m

let rec close_exp_ln (e:stlc_exp 'a) (v:var) (n:nat)
  : Lemma 
    (requires ln' e (n - 1))
    (ensures ln' (close_exp' e v n) n)
    [SMTPat (ln' (close_exp' e v n) n)]
  = match e with
    | EUnit -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | ELam _ e -> close_exp_ln e v (n + 1)
    | EApp e1 e2 -> close_exp_ln e1 v n; close_exp_ln e2 v n
    
let s_exp = e:stlc_exp stlc_ty

let stlc_env = list (var & stlc_ty)

let lookup (e:list (var & 'a)) (x:var)
  : option 'a
  = L.assoc x e

let max (n1 n2:nat) = if n1 < n2 then n2 else n1

let rec fresh (e:list (var & 'a))
  : var
  = match e with
    | [] -> 0
    | hd :: tl -> 
      max (fresh tl) (fst hd) + 1

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

let fresh_is_fresh (e:list (var & 'a))
  : Lemma (None? (lookup e (fresh e)))
  =  match lookup e (fresh e) with
     | None -> ()
     | Some _ ->
       lookup_mem e (fresh e);
       FStar.Classical.forall_intro (fresh_not_mem e)
  
[@@erasable]
noeq
type stlc_typing : stlc_env -> s_exp -> stlc_ty -> Type =
  | T_Unit :
      g:stlc_env ->
      stlc_typing g EUnit TUnit
  
  | T_Var  :
      g:stlc_env ->
      x:var { Some? (lookup g x) } ->
      stlc_typing g (EVar x) (Some?.v (lookup g x))

  | T_Lam  :
      g:stlc_env ->
      t:stlc_ty ->
      e:s_exp ->
      t':stlc_ty ->
      x:var { x == fresh g } ->
      stlc_typing ((x,t)::g) (open_exp e x) t' ->
      stlc_typing g (ELam t e) (TArrow t t')

  | T_App  :
      g:stlc_env ->
      e1:s_exp ->
      e2:s_exp ->
      t:stlc_ty ->
      t':stlc_ty ->
      stlc_typing g e1 (TArrow t t') ->
      stlc_typing g e2 t ->
      stlc_typing g (EApp e1 e2) t'
  
let new_hole (g:R.env)
  : T.Tac R.term
  = T.uvar_env g (Some (`stlc_ty))
    
let rec infer (g:R.env)
              (sg:list (var & R.term))
              (e:stlc_exp unit { ln e })
  : T.Tac (e:stlc_exp R.term { ln e } & R.term)
  = match e with
    | EUnit ->
      (| EUnit, `TUnit |)


    | EVar x ->
      begin
      match lookup sg x with
      | None -> T.fail "Unbound variable"
      | Some ht -> (| EVar x, ht |)
      end

    | ELam _ e ->
      let t0 = new_hole g in
      let x = fresh sg in
      let (| e, t |) = infer g ((x, t0) :: sg) (open_exp e x) in
      (| ELam t (close_exp e x), `(TArrow (`#(t0)) (`#(t))) |)

    | EApp e1 e2 ->
      let (| e1, t1 |) = infer g sg e1 in
      let (| e2, t2 |) = infer g sg e2 in
      let res = new_hole g in
      let ht = (`TArrow (`#(t2)) (`#(res))) in
      if T.unify_env g t1 ht
      then (| EApp e1 e2, res |)
      else T.fail ("Expected arrow type " ^ T.term_to_string res ^ 
                   " Got " ^ T.term_to_string t1)

let is_fv (t:R.term) (n:R.name)
  : T.Tac bool
  = match T.inspect t with
    | R.Tv_FVar fv ->
      R.inspect_fv fv = n
    | _ -> false
   
let rec read_back (g:R.env) (t:R.term)
  : T.Tac stlc_ty
  = let tt = T.inspect t in
    match tt with
    | R.Tv_Uvar _ _ -> 
      if T.unify_env g t (`TUnit)
      then read_back g t
      else T.fail "Impossible: Unresolved uvar must be unifiable with TUnit"
      
    | R.Tv_FVar _ ->
      if is_fv t ["STLC"; "TUnit"]
      then TUnit
      else T.fail "Got an FV of type stlc_ty, but it is not a TUnit"

    | R.Tv_App _ _ ->
      begin
      let head, args = R.collect_app t in
      if not (is_fv head ["STLC"; "TArrow"])
      then T.fail "Got an application of type stlc_ty, but head is not a TArrow"
      else match args with
           | [t1;t2] ->
             let t1 = read_back g (fst t1) in
             let t2 = read_back g (fst t2) in
             TArrow t1 t2
             
           | _ -> T.fail "Impossible: Incorrect arity of arrow"
      end

    | _ -> 
      T.fail "Unexpected constructor of stlc_ty"
  
let rec check (g:R.env)
              (sg:list (var & stlc_ty))
              (e:stlc_exp R.term { ln e })
  : T.Tac (e':s_exp { ln e' } &
           t':stlc_ty &
           stlc_typing sg e' t')
  = match e with
    | EUnit ->
      let d = T_Unit sg in
      (| EUnit, TUnit, d |)
      
    | EVar n ->
      begin
      match lookup sg n with
      | None -> T.fail "Ill-typed"
      | Some t ->
        let d = T_Var sg n in
        (| EVar n, t, d |)
      end

    | ELam rt e ->
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

let stlc_types_are_closed3 (ty:stlc_ty) (x:R.var)
  : Lemma (RT.open_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.open_term (elab_ty ty) x)]
  = admit()

let fstar_env =
  g:R.env { 
    RT.lookup_fvar g RT.unit_fv == Some RT.tm_type
  }

let fstar_top_env =
  g:fstar_env { 
    forall x. None? (RT.lookup_bvar g x )
  }

let extend_env_l_lookup_fvar (g:R.env) (sg:stlc_env) (fv:R.fv)
  : Lemma 
    (ensures
      RT.lookup_fvar (extend_env_l g sg) fv ==
      RT.lookup_fvar g fv)
    [SMTPat (RT.lookup_fvar (extend_env_l g sg) fv)]
  = admit()
          
let rec elab_ty_soundness (g:fstar_top_env)
                          (sg:stlc_env)
                          (t:stlc_ty)
  : GTot (RT.typing (extend_env_l g sg) (elab_ty t) RT.tm_type)
         (decreases t)
  = match t with
    | TUnit -> 
      RT.T_FVar _ RT.unit_fv
      
    | TArrow t1 t2 ->
      let t1_ok = elab_ty_soundness g sg t1 in
      let x = fresh sg in
      fresh_is_fresh sg;
      let t2_ok = elab_ty_soundness g ((x, t1)::sg) t2 in
      RT.T_Arrow _ x (elab_ty t1) (elab_ty t2) t1_ok t2_ok
  
let rec soundness (#sg:stlc_env) 
                  (#se:s_exp)
                  (#st:stlc_ty)
                  (dd:stlc_typing sg se st)
                  (g:fstar_top_env)
  : GTot (RT.typing (extend_env_l g sg)
                    (elab_exp se)
                    (elab_ty st))
         (decreases dd)
  = match dd with
    | T_Unit _ ->
      RT.T_Const _ _ _ RT.CT_Unit

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
                   (elab_ty_soundness g sg t)
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
                    (g:fstar_top_env)
  : Lemma
    (requires stlc_typing sg se st)
    (ensures  RT.typing (extend_env_l g sg)
                        (elab_exp se)
                        (elab_ty st))
  = FStar.Squash.bind_squash 
      #(stlc_typing sg se st)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness dd g))

let main (g:fstar_top_env)
         (src:stlc_exp unit)
  : T.Tac (e:R.term & t:R.term { RT.typing g e t })
  = if ln src
    then 
      let (| src', src_ty |) = infer_and_check g src in
      soundness_lemma [] src' src_ty g;
      (| elab_exp src', elab_ty src_ty |)
    else T.fail "Not locally nameless"
