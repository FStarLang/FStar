module STLC.Core
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module RT = FStar.Reflection.Typing

type stlc_ty =
  | TUnit
  | TArrow : stlc_ty -> stlc_ty -> stlc_ty

let var = nat
let index = nat

noeq
type stlc_exp =
  | EUnit : stlc_exp
  | EBVar : index -> stlc_exp
  | EVar  : var -> stlc_exp
  | ELam  : stlc_ty -> stlc_exp -> stlc_exp
  | EApp  : stlc_exp -> stlc_exp -> stlc_exp

let rec size (e:stlc_exp) 
  : nat
  = match e with
    | EUnit
    | EBVar _ 
    | EVar _ -> 1
    | ELam _ e -> 1 + size e
    | EApp e1 e2 -> 1 + size e1 + size e2

let rec ln' (e:stlc_exp) (n:int)
  : bool
  = match e with
    | EUnit
    | EVar _ -> true
    | EBVar m -> m <= n
    | ELam _ e -> ln' e (n + 1)
    | EApp e1 e2 -> ln' e1 n && ln' e2 n

let ln e = ln' e (-1)
    
let rec open_exp' (e:stlc_exp) (v:var) (n:index)
  : e':stlc_exp { size e == size e'}
  = match e with
    | EUnit -> EUnit
    | EVar m -> EVar m
    | EBVar m -> if m = n then EVar v else EBVar m
    | ELam t e -> ELam t (open_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (open_exp' e1 v n) (open_exp' e2 v n)

let rec close_exp' (e:stlc_exp) (v:var) (n:nat)
  : e':stlc_exp { size e == size e'}
  = match e with
    | EUnit -> EUnit
    | EVar m -> if m = v then EBVar n else EVar m
    | EBVar m -> EBVar m
    | ELam t e -> ELam t (close_exp' e v (n + 1))
    | EApp e1 e2 -> EApp (close_exp' e1 v n) (close_exp' e2 v n)

let open_exp e v = open_exp' e v 0
let close_exp e v = close_exp' e v 0

let rec open_close' (e:stlc_exp) (x:var) (n:nat { ln' e (n - 1) })
  : Lemma (open_exp' (close_exp' e x n) x n == e)
  = match e with
    | EUnit -> ()
    | EVar _ -> ()
    | EBVar m -> ()
    | ELam _ e -> open_close' e x (n + 1)
    | EApp e1 e2 -> 
      open_close' e1 x n; 
      open_close' e2 x n

let open_close (e:stlc_exp) (x:var)
  : Lemma 
    (requires ln e)
    (ensures open_exp (close_exp e x) x == e)
    [SMTPat (open_exp (close_exp e x) x)]
  = open_close' e x 0

let rec open_exp_ln (e:stlc_exp) (v:var) (n:index) (m:int)
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

let rec close_exp_ln (e:stlc_exp) (v:var) (n:nat)
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

let rec freevars (e:stlc_exp)
  : Set.set var
  = match e with
    | EUnit 
    | EBVar _ -> Set.empty
    | EVar x -> Set.singleton x
    | ELam _ e -> freevars e
    | EApp e1 e2 -> freevars e1 `Set.union` freevars e2
    
let rec closed (e:stlc_exp) 
  : b:bool { b <==>  (freevars e `Set.equal` Set.empty) }
  = match e with
    | EUnit 
    | EBVar _ -> true
    | EVar x -> 
      assert (x `Set.mem` freevars e);
      false
    | ELam _ e -> closed e
    | EApp e1 e2 -> closed e1 && closed e2
  
let rec freevars_open (e:stlc_exp) (x:var) (n:nat)
  : Lemma (freevars (open_exp' e x n) `Set.subset`
          (freevars e `Set.union` Set.singleton x))
  = match e with
    | EUnit 
    | EBVar _
    | EVar _ -> ()
    | ELam _ e -> freevars_open e x (n + 1)
    | EApp e1 e2 ->
      freevars_open e1 x n;
      freevars_open e2 x n

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

let _ = assert (fresh [1,();2,();3,();4,()] == 8) // odd.. but ok

let rec fresh_not_mem (e:list (var & 'a)) (elt: (var & 'a))
  : Lemma (ensures L.memP elt e ==> fresh e > fst elt)
  = match e with
    | [] -> ()
    | hd :: tl -> fresh_not_mem tl elt

let lookup_mem (e:list (var & 'a)) (x:var)
  : Lemma
    (requires Some? (lookup e x))
    (ensures exists elt. L.memP elt e /\ fst elt == x)
  = let Some y = lookup e x in
    List.Tot.Properties.assoc_memP_some x y e

let fresh_is_fresh (e:list (var & 'a))
  : Lemma (None? (lookup e (fresh e)))
  =  match lookup e (fresh e) with
     | None -> ()
     | Some _ ->
       lookup_mem e (fresh e);
       FStar.Classical.forall_intro (fresh_not_mem e)
  
[@@erasable]
noeq
type stlc_typing : stlc_env -> stlc_exp -> stlc_ty -> Type =
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
      e:stlc_exp ->
      t':stlc_ty ->
      x:var { None? (lookup g x) /\ ~ (Set.mem x (freevars e)) } ->
      stlc_typing ((x,t)::g) (open_exp e x) t' ->
      stlc_typing g (ELam t e) (TArrow t t')

  | T_App  :
      g:stlc_env ->
      e1:stlc_exp ->
      e2:stlc_exp ->
      t:stlc_ty ->
      t':stlc_ty ->
      stlc_typing g e1 (TArrow t t') ->
      stlc_typing g e2 t ->
      stlc_typing g (EApp e1 e2) t'


let tun = R.pack_ln R.Tv_Unknown

let rec ty_to_string' should_paren (t:stlc_ty)
  : Tot string (decreases t)
  = match t with
    | TUnit -> "unit"
    | TArrow t1 t2 -> 
      let t = Printf.sprintf "%s -> %s"
                 (ty_to_string' true t1)
                 (ty_to_string' false t2) in
      if should_paren 
      then Printf.sprintf "(%s)" t
      else t
      
let ty_to_string = ty_to_string' false

let mem_intension_pat (#a:eqtype) (x:a) (f:(a -> Tot bool))
  : Lemma
    (ensures FStar.Set.(mem x (intension f) = f x))
    [SMTPat FStar.Set.(mem x (intension f))]
  = Set.mem_intension x f

let contains (sg:list (var & stlc_ty)) (x:var) = 
  Some? (lookup sg x)
  
let vars_of_env (sg:list (var & stlc_ty))
  : GTot (Set.set var)
  = Set.intension (contains sg)

let rec check (g:R.env)
              (sg:list (var & stlc_ty))
              (e:stlc_exp { ln e /\ (freevars e `Set.subset` vars_of_env sg)})
  : T.Tac (t:stlc_ty &
           stlc_typing sg e t)
  = match e with
    | EUnit ->
      let d = T_Unit sg in
      (| TUnit, d |)
      
    | EVar n ->
      begin
      match lookup sg n with
      | None -> T.fail "Ill-typed"
      | Some t ->
        let d = T_Var sg n in
        (| t, d |)
      end

    | ELam t e ->
      let x = fresh sg in
      fresh_is_fresh sg;
      freevars_open e x 0;
      let (| tbody, dbody |) = check g ((x,t)::sg) (open_exp e x) in
      (| TArrow t tbody, 
         T_Lam sg t e tbody x dbody |)
           
    | EApp e1 e2 ->
      let (| t1, d1 |) = check g sg e1  in
      let (| t2, d2 |) = check g sg e2 in
      match t1 with
      | TArrow t2' t ->
        if t2' = t2
        then (| t, T_App _ _ _ _ _ d1 d2 |)
        else T.fail 
               (Printf.sprintf "Expected argument of type %s got %s"
                               (ty_to_string t2')
                               (ty_to_string t2))
        
      | _ -> 
        T.fail (Printf.sprintf "Expected an arrow, got %s"
                               (ty_to_string t1))

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
          (RT.mk_simple_binder RT.pp_name_default t1)
          (R.pack_comp (C_Total t2)))
  
let rec elab_exp (e:stlc_exp)
  : Tot R.term (decreases (size e))
  = let open R in
    match e with
    | EUnit -> 
      pack_ln (Tv_Const C_Unit)

    | EBVar n -> 
      let bv = R.pack_bv (RT.make_bv n) in
      R.pack_ln (Tv_BVar bv)
      
    | EVar n ->
      let bv = R.pack_namedv (RT.make_namedv n) in
      R.pack_ln (Tv_Var bv)

    | ELam t e ->
      let t = elab_ty t in
      let e = elab_exp e in
      R.pack_ln (Tv_Abs (RT.mk_simple_binder RT.pp_name_default t) e)
             
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


open FStar.Calc

//key lemma about STLC types: Their elaborations are closed
let rec stlc_types_are_closed_core (ty:stlc_ty) (ss:RT.subst)
  : Lemma (ensures RT.subst_term (elab_ty ty) ss == elab_ty ty)
          (decreases ty)
          [SMTPat (RT.subst_term (elab_ty ty) ss)]

  = match ty with
    | TUnit -> ()
    | TArrow t1 t2 ->
      stlc_types_are_closed_core t1 ss;
      stlc_types_are_closed_core t2 (RT.shift_subst ss)

let stlc_types_are_closed1 (ty:stlc_ty) (v:R.term)
  : Lemma (RT.open_with (elab_ty ty) v == elab_ty ty)
          [SMTPat (RT.open_with (elab_ty ty) v)]
  = stlc_types_are_closed_core ty [ RT.DT 0 v ];
    RT.open_with_spec (elab_ty ty) v

let stlc_types_are_closed2 (ty:stlc_ty) (x:R.var)
  : Lemma (RT.close_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.close_term (elab_ty ty) x)]
  = stlc_types_are_closed_core ty [ RT.ND x 0 ];
    RT.close_term_spec (elab_ty ty) x

let stlc_types_are_closed3 (ty:stlc_ty) (x:R.var)
  : Lemma (RT.open_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.open_term (elab_ty ty) x)]
  = stlc_types_are_closed_core ty [ RT.DT 0 (RT.var_as_term x) ];
    RT.open_term_spec (elab_ty ty) x

let rec elab_ty_freevars (ty:stlc_ty)
  : Lemma (RT.freevars (elab_ty ty) `Set.equal` Set.empty)
  = match ty with
    | TUnit -> ()
    | TArrow t1 t2 ->
      elab_ty_freevars t1;
      elab_ty_freevars t2
      
let rec elab_open_commute' (e:stlc_exp) (x:var) (n:nat)
  : Lemma (ensures
              RT.subst_term (elab_exp e) (RT.open_with_var x n) ==
              elab_exp (open_exp' e x n))
          (decreases e)
  = match e with
    | EUnit -> ()
    | EBVar _ -> ()
    | EVar _ -> ()
    | EApp e1 e2 -> 
      elab_open_commute' e1 x n;
      elab_open_commute' e2 x n
    | ELam t e ->
      calc (==) {
        elab_exp (open_exp' (ELam t e) x n);
      (==) {}
        elab_exp (ELam t (open_exp' e x (n + 1)));      
      (==) {  }
        R.(pack_ln (Tv_Abs (RT.mk_simple_binder RT.pp_name_default (elab_ty t)) (elab_exp (open_exp' e x (n + 1)))));
      (==) { elab_open_commute' e x (n + 1) } 
        R.(pack_ln (Tv_Abs (RT.mk_simple_binder RT.pp_name_default (elab_ty t))
                           (RT.subst_term (elab_exp e) RT.(open_with_var x (n + 1)))));
      (==) { stlc_types_are_closed_core t (RT.open_with_var x n) }
        RT.subst_term
          R.(pack_ln (Tv_Abs (RT.mk_simple_binder RT.pp_name_default (elab_ty t)) (elab_exp e)))
          RT.(open_with_var x n);
      }

let elab_open_commute (e:stlc_exp) (x:var)
  : Lemma (RT.open_term (elab_exp e) x == elab_exp (open_exp e x))
          [SMTPat (RT.open_term (elab_exp e) x)]
  = elab_open_commute' e x 0;
    RT.open_term_spec (elab_exp e) x

let rec extend_env_l_lookup_fvar (g:R.env) (sg:stlc_env) (fv:R.fv)
  : Lemma 
    (ensures
      RT.lookup_fvar (extend_env_l g sg) fv ==
      RT.lookup_fvar g fv)
    [SMTPat (RT.lookup_fvar (extend_env_l g sg) fv)]
  = match sg with
    | [] -> ()
    | hd::tl -> extend_env_l_lookup_fvar g tl fv
   
let rec elab_ty_soundness (g:RT.fstar_top_env)
                          (sg:stlc_env)
                          (t:stlc_ty)
  : GTot (RT.tot_typing (extend_env_l g sg) (elab_ty t) (RT.tm_type RT.u_zero))
         (decreases t)
  = match t with
    | TUnit -> 
      RT.T_FVar _ RT.unit_fv
      
    | TArrow t1 t2 ->
      let t1_ok = elab_ty_soundness g sg t1 in
      let x = fresh sg in
      fresh_is_fresh sg;
      elab_ty_freevars t2;
      let t2_ok = elab_ty_soundness g ((x, t1)::sg) t2 in
      let arr_max 
        : RT.tot_typing 
               (extend_env_l g sg)
               (elab_ty t)
               (RT.tm_type RT.(u_max u_zero u_zero))
            =  RT.T_Arrow _ x (elab_ty t1) (elab_ty t2) 
                          _ _ RT.pp_name_default R.Q_Explicit T.E_Total _ _ t1_ok t2_ok
      in
      RT.simplify_umax arr_max

let rec elab_exp_freevars (e:stlc_exp)
  : Lemma (freevars e `Set.equal` RT.freevars (elab_exp e))
  = match e with
    | EUnit
    | EBVar _
    | EVar _ -> ()
    | ELam t e ->
      elab_ty_freevars t;
      elab_exp_freevars e
    | EApp e1 e2 ->
      elab_exp_freevars e1;
      elab_exp_freevars e2
    
let rec soundness (#sg:stlc_env) 
                  (#se:stlc_exp)
                  (#st:stlc_ty)
                  (dd:stlc_typing sg se st)
                  (g:RT.fstar_top_env)
  : GTot (RT.tot_typing (extend_env_l g sg)
                        (elab_exp se)
                        (elab_ty st))
         (decreases dd)
  = match dd with
    | T_Unit _ ->
      RT.T_Const _ _ _ RT.CT_Unit

    | T_Var _ x ->
      RT.T_Var _ (R.pack_namedv (RT.make_namedv x))

    | T_Lam _ t e t' x de ->
      let de : RT.tot_typing (extend_env_l g ((x,t)::sg))
                             (elab_exp (open_exp e x))
                             (elab_ty t')
            = soundness de g 
      in    
      let de : RT.tot_typing (RT.extend_env (extend_env_l g sg) x (elab_ty t))
                             (elab_exp (open_exp e x))
                             (elab_ty t')
             = de
      in
      fresh_is_fresh sg;
      elab_exp_freevars e;
      let dd
        = RT.T_Abs (extend_env_l g sg)
                   x
                   (elab_ty t) 
                   (elab_exp e)
                   (T.E_Total, elab_ty t')
                   _
                   RT.pp_name_default
                   R.Q_Explicit
                   _
                   (elab_ty_soundness g sg t)
                   de
      in
      dd
    | T_App _ e1 e2 t t' d1 d2 ->
      let dt1 
        : RT.tot_typing (extend_env_l g sg)
                        (elab_exp e1)
                        (elab_ty (TArrow t t'))
        = soundness d1 g
      in
      let dt2
        : RT.tot_typing (extend_env_l g sg)
                        (elab_exp e2)
                        (elab_ty t)
        = soundness d2 g
      in
      let dt :
        RT.tot_typing (extend_env_l g sg)
                      (elab_exp (EApp e1 e2))
                      (RT.open_with (elab_ty t') (elab_exp e2))
        = RT.T_App _ _ _ _ _ _ dt1 dt2
      in
      dt

let soundness_lemma (sg:stlc_env) 
                    (se:stlc_exp)
                    (st:stlc_ty)
                    (g:RT.fstar_top_env)
  : Lemma
    (requires stlc_typing sg se st)
    (ensures  RT.tot_typing (extend_env_l g sg)
                            (elab_exp se)
                            (elab_ty st))
  = FStar.Squash.bind_squash 
      #(stlc_typing sg se st)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness dd g))

let main (src:stlc_exp) : RT.dsl_tac_t =
  fun g ->
  if ln src && closed src
  then
    let (| src_ty, d |) = check g [] src in
    soundness_lemma [] src src_ty g;
    elab_exp src, elab_ty src_ty
  else T.fail "Not locally nameless"

(***** Tests *****)

%splice_t[foo] (main (ELam TUnit (EBVar 0)))

#push-options "--no_smt"
let test_id () = assert (foo () == ()) by (T.compute ())
#pop-options

let bar_s = (ELam TUnit (ELam TUnit (EBVar 1)))
%splice_t[bar] (main bar_s)

let baz_s : stlc_exp = EApp bar_s EUnit
%splice_t[baz] (main bar_s)
