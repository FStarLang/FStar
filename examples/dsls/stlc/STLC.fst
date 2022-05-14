module STLC
module T = FStar.Tactics
module R = FStar.Reflection
module L = FStar.List.Tot

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

let open_close (e:stlc_exp 'a) (x:var)
  : Lemma (open_exp (close_exp e x) x == e)
          [SMTPat (open_exp (close_exp e x) x)]
  = admit()
  
let s_exp = stlc_exp stlc_ty

let stlc_env = list (var & stlc_ty)

let lookup (e:list (var & 'a)) (x:var)
  : option 'a
  = L.assoc x e

let max (n1 n2:nat) = if n1 < n2 then n2 else n1

let fresh (e:list (var & 'a))
  : var
  = L.fold_right (fun (n, _) v -> max v n) e 0 + 1

let fresh_is_fresh (e:list (var & 'a))
  : Lemma (None? (lookup e (fresh e)))
  = admit()
  
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
              (e:stlc_exp unit)
  : T.Tac (stlc_exp R.term & R.term)
  = match e with
    | EUnit ->
      EUnit, `TUnit

    | EBVar _ -> 
      T.fail "Locally nameless"
      
    | EVar x ->
      begin
      match lookup sg x with
      | None -> T.fail "Unbound variable"
      | Some ht -> EVar x, ht
      end

    | ELam _ e ->
      let t0 = new_hole g in
      let x = fresh sg in
      let e, t = infer g ((x, t0) :: sg) (open_exp e x) in
      ELam t e, `(TArrow (`#(t0)) (`#(t)))

    | EApp e1 e2 ->
      let e1, t1 = infer g sg e1 in
      let e2, t2 = infer g sg e2 in
      let res = new_hole g in
      let ht = (`TArrow (`#(t2)) (`#(res))) in
      if T.unify_env g t1 ht
      then EApp e1 e2, res
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
              (e:stlc_exp R.term)
  : T.Tac (e':s_exp &
           t':stlc_ty &
           stlc_typing sg e' t')
  = match e with
    | EUnit ->
      let d = T_Unit sg in
      (| EUnit, TUnit, d |)
      
    | EBVar _ -> 
      T.fail "Locally nameless"

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
                    (e:stlc_exp unit)
  : T.Tac (e':s_exp &
           t :stlc_ty { stlc_typing [] e' t })
  = let e', _ = infer g [] e in
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

let make_bv (n:nat) (t:R.term) = R.({ bv_ppname = ""; bv_index = n; bv_sort = t})
let bv_as_binder bv = R.pack_binder bv R.Q_Explicit []
let bv_index_of_make_nv (n:nat) (t:R.term)
  : Lemma (ensures RT.bv_index (R.pack_bv (make_bv n t)) == n)
          [SMTPat (RT.bv_index (R.pack_bv (make_bv n t)))]
  = admit()
  
let rec elab_exp (e:s_exp)
  : Tot R.term (decreases (size e))
  = let open R in
    match e with
    | EUnit -> 
      pack_ln (Tv_Const C_Unit)

    | EBVar n -> 
      let bv = R.pack_bv (make_bv n tun) in
      R.pack_ln (Tv_BVar bv)
      
    | EVar n ->
      // tun because type does not matter at a use site
      let bv = R.pack_bv (make_bv n tun) in
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
  L.fold_left (fun g (x, t) -> RT.extend_env g x (elab_ty t)) g sg

let extend_env_l_lookup_bvar (g:R.env) (sg:stlc_env) (x:var)
  : Lemma 
    (requires (forall x. RT.lookup_bvar g x == None))
    (ensures (
      match lookup sg x with
      | Some t -> RT.lookup_bvar (extend_env_l g sg) x == Some (elab_ty t)
      | None -> RT.lookup_bvar (extend_env_l g sg) x == None))
    [SMTPat (RT.lookup_bvar (extend_env_l g sg) x)]
  = admit()

let binder_sort_lemma (x:R.var) (ty:R.term)
  : Lemma (RT.binder_sort (RT.as_binder x ty) == ty)
          [SMTPat (RT.binder_sort (RT.as_binder x ty))]
  = admit()          

let elab_open_commute (e:s_exp) (x:var)
  : Lemma (RT.open_term (elab_exp e) x == elab_exp (open_exp e x))
          [SMTPat (RT.open_term (elab_exp e) x)]
  = admit()

let extend_env_cons (g:R.env)
                    (sg:stlc_env)
                    (x:var)
                    (t:stlc_ty)
   : Lemma 
     (ensures (extend_env_l g ((x,t)::sg)) == RT.extend_env (extend_env_l g sg) x (elab_ty t))
     [SMTPat (extend_env_l g ((x,t)::sg))]
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
      RT.T_Var _ (R.pack_bv (make_bv x tun))

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
  = let (| src', src_ty |) = infer_and_check g src in
    soundness_lemma [] src' src_ty g;
    (| elab_exp src', elab_ty src_ty |)
