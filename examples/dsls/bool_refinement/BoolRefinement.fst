module BoolRefinement
module T = FStar.Tactics
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
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

let rec size (e:src_exp)
  : nat
  = match e with
    | EBool _
    | EBVar _ 
    | EVar _ -> 1
    | EIf b e1 e2 -> size b + size e1 + size e2 + 1
    | ELam _ e -> 1 + size e
    | EApp e1 e2 -> 1 + size e1 + size e2

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
  
let rec closed (e:src_exp) 
  : b:bool{ b <==> freevars e `Set.equal` Set.empty }
  = match e with
    | EVar v -> 
      assert (v `Set.mem` freevars e);
      false
    | EBool _
    | EBVar _ -> true
    | EIf b e1 e2 -> closed b && closed e1 && closed e2
    | ELam t e -> closed_ty t && closed e
    | EApp e1 e2 -> closed e1 && closed e2
and closed_ty (t:src_ty)
  : b:bool{ b <==> freevars_ty t `Set.equal` Set.empty }
  = match t with
    | TBool -> true
    | TRefineBool e -> closed e
    | TArrow t1 t2 -> closed_ty t1 && closed_ty t2
  
let rec ln' (e:src_exp) (n:int)
  : bool
  = match e with
    | EBool _
    | EVar _ -> true
    | EBVar m -> m <= n
    | EIf b e1 e2 -> ln' b n && ln' e1 n && ln' e2 n
    | ELam t e -> ln_ty t && ln' e (n + 1)
    | EApp e1 e2 -> ln' e1 n && ln' e2 n
and ln_ty (e:src_ty)
  : b:bool{ b ==> closed_ty e }
  = match e with
    | TBool -> true
    | TRefineBool e -> ln' e (- 1) && closed e
    | TArrow t1 t2 -> ln_ty t1 && ln_ty t2

let rec ln_weaker (e:src_exp) (n:int) (m:int{n <= m})
  : Lemma 
    (requires ln' e n)
    (ensures ln' e m)
  = match e with
    | EBool _
    | EVar _
    | EBVar _ -> ()
    | EIf b e1 e2 -> 
      ln_weaker b n m;
      ln_weaker e1 n m;
      ln_weaker e2 n m
    | ELam t e ->
      ln_weaker e (n + 1) (m + 1)
    | EApp e1 e2 ->
      ln_weaker e1 n m;
      ln_weaker e2 n m    

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

let rec open_exp_freevars (e:src_exp) (v:var) (n:nat)
  : Lemma ((freevars e `Set.subset` freevars (open_exp' e v n))  /\
           (freevars (open_exp' e v n) `Set.subset` (freevars e `Set.union` Set.singleton v)))
          [SMTPat (freevars (open_exp' e v n))]
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
      open_exp_freevars e v (n + 1)
      
let minus (s:Set.set 'a) (x:'a) = Set.intersect s (Set.complement (Set.singleton x))

let rec close_exp_freevars (m:int) (e:src_exp { ln' e m } ) (v:var) (n:nat)
  : Lemma 
    (ensures freevars (close_exp' e v n) `Set.equal`
             (freevars e `minus` v))
    (decreases e)
  = match e with
    | EBool _
    | EBVar _ 
    | EVar _ -> ()
    | EApp e1 e2 ->
      close_exp_freevars m e1 v n;
      close_exp_freevars m e2 v n
    | EIf b e1 e2 ->
      close_exp_freevars m b v n;    
      close_exp_freevars m e1 v n;
      close_exp_freevars m e2 v n
    | ELam t body ->
      close_exp_freevars (m + 1) body v (n + 1)

let s_exp = e:src_exp { ln e }
let src_eqn = s_exp & s_exp

let s_ty = t:src_ty { ln_ty t }
//environment binds types or equations
let src_env = list (var & either s_ty src_eqn) 

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

let binding = either s_ty src_eqn
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

let as_bindings (sg:src_env) 
  : RT.bindings
  = L.map (fun (x, b) -> x, elab_binding b) sg

let extend_env_alt (g:R.env) (sg:src_env) = 
  RT.extend_env_l g (as_bindings sg)

let rec extend_env_equiv (g:R.env) (sg:src_env)
  : Lemma 
    (ensures extend_env_l g sg == extend_env_alt g sg)
    (decreases sg)
  = match sg with
    | [] -> ()
    | hd::tl -> extend_env_equiv g tl

let rec extend_env_alt_append (g:R.env) (sg0 sg1:src_env)
  : Lemma 
    (ensures 
      extend_env_alt g (sg0 @ sg1) == 
      extend_env_alt (extend_env_alt g sg1) sg0)
    (decreases sg0)
  = match sg0 with
    | [] -> ()
    | hd::tl -> extend_env_alt_append g tl sg1
           
let fstar_env =
  g:R.env { 
    RT.lookup_fvar g RT.bool_fv == Some RT.tm_type /\
    RT.lookup_fvar g b2t_fv == Some b2t_ty
  }

let fstar_top_env =
  g:fstar_env { 
    forall x. None? (RT.lookup_bvar g x )
  }

[@@erasable]
noeq
type sub_typing (f:fstar_top_env) : src_env -> s_ty -> s_ty -> Type =
  | S_Refl : g:src_env -> t:s_ty -> sub_typing f g t t
  | S_ELab : g:src_env -> t0:s_ty -> t1:s_ty ->
             RT.sub_typing (extend_env_l f g) (elab_ty t0) (elab_ty t1) ->
             sub_typing f g t0 t1

  
[@@erasable]
noeq
type src_typing (f:fstar_top_env) : src_env -> src_exp -> s_ty -> Type =
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
      t:s_ty ->
      e:src_exp ->
      t':s_ty ->
      x:var { None? (lookup g x) /\ ~ (x `Set.mem` freevars e)} ->
      src_ty_ok f g t ->
      src_typing f ((x, Inl t) :: g) (open_exp e x) t' ->
      src_typing f g (ELam t e) (TArrow t t')

  | T_App  :
      g:src_env ->
      e1:src_exp ->
      e2:src_exp ->
      t:s_ty ->
      t':s_ty ->
      t0:s_ty ->
      src_typing f g e1 (TArrow t t') ->
      src_typing f g e2 t0 ->
      sub_typing f g t0 t ->
      src_typing f g (EApp e1 e2) t'

   | T_If :
       g:src_env ->
       b:s_exp ->
       e1:src_exp ->
       e2:src_exp ->
       t1:s_ty ->
       t2:s_ty ->
       t:s_ty ->
       hyp:var { None? (lookup g hyp) /\ ~ (hyp `Set.mem` freevars e1) /\ ~ (hyp `Set.mem` freevars e2) } ->
       src_typing f g b TBool ->
       src_typing f ((hyp, Inr (b, EBool true)) :: g) e1 t1 ->
       src_typing f ((hyp, Inr (b, EBool false)) :: g) e2 t2 ->
       sub_typing f ((hyp, Inr (b, EBool true)) :: g) t1 t ->
       sub_typing f ((hyp, Inr (b, EBool false)) :: g) t2 t ->
       src_typing f g (EIf b e1 e2) t
       
and src_ty_ok (f:fstar_top_env) : src_env -> s_ty -> Type =
  | OK_TBool  : g:src_env -> src_ty_ok f g TBool
  | OK_TArrow : g:src_env -> t:s_ty -> t':s_ty ->
                src_ty_ok f g t ->
                src_ty_ok f g t' ->                
                src_ty_ok f g (TArrow t t')
  | OK_TRefine: g:src_env ->
                e:src_exp { ln e && closed e}  ->
                src_typing f [] e (TArrow TBool TBool) ->
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
    
and t_height #f (#g:src_env) (#t:s_ty) (d:src_ty_ok f g t)    
  : GTot nat (decreases d)
  = match d with
    | OK_TBool _ -> 1
    | OK_TArrow _ _ _ d0 d1 -> max (t_height d0) (t_height d1) + 1
    | OK_TRefine _ _ d -> height d + 1

let check_sub_typing f
                     (sg:src_env)
                     (t0 t1:s_ty)
  : T.Tac (sub_typing f sg t0 t1)
  = if t0 = t1 then S_Refl _ t0
    else T.fail "Not subtypes"

let weaken (f:fstar_top_env) (sg:src_env) (hyp:var { None? (lookup sg hyp) } ) (b:s_exp) (t0 t1:s_ty)
  : T.Tac (t:s_ty &
           sub_typing f ((hyp,Inr(b, EBool true))::sg) t0 t &
           sub_typing f ((hyp,Inr(b, EBool false))::sg) t1 t)
  = if t0 = t1
    then (| t0, S_Refl _ t0, S_Refl _ t1 |)
    else T.fail "weaken is very dumb"

let exp (sg:src_env) = e:src_exp { ln e /\ (forall x. x `Set.mem` freevars e ==> Some? (lookup sg x)) }

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 6 --query_stats"
let rec check (f:fstar_top_env)
              (sg:src_env)
              (e:exp sg)
  : T.Tac (t:s_ty &
           src_typing f sg e t)
  = match e with
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
      let (| tbody, dbody |) = check f ((x, Inl t)::sg) (open_exp body x) in
      let e' = ELam t body in
      let dd : src_typing f sg e' (TArrow t tbody) = 
             T_Lam sg t body tbody x t_ok dbody in
      (| TArrow t tbody, dd |)

    | EApp e1 e2 ->
      let (| t1, d1 |) = check f sg e1  in
      let (| t2, d2 |) = check f sg e2 in
      begin
      match t1 with
      | TArrow t_arg t_res ->
        let st_ok = check_sub_typing f sg t2 t_arg in
        (| t_res, T_App _ _ _ t_arg t_res _ d1 d2 st_ok |)

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
             (t:s_ty)
  : T.Tac (src_ty_ok f sg t)
  = match t with
    | TBool -> OK_TBool _

    | TArrow t t' ->
      let t_ok  = check_ty f sg t in
      let t'_ok = check_ty f sg t' in      
      OK_TArrow _ _ _ t_ok t'_ok
      
    | TRefineBool e ->
      let (| te, de |) = check f [] e in
      match te with
      | TArrow TBool TBool -> OK_TRefine _ _ de
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

//key lemma about src types: Their elaborations are closed
let rec src_refinements_are_closed_core
                       (n:nat)
                       (e:src_exp {ln' e (n - 1) && closed e}) 
                       (x:RT.open_or_close)
  : Lemma (ensures RT.open_or_close_term' (elab_exp e) x n == elab_exp e)
          (decreases e)
  = match e with
    | EBool _ -> ()
    | EBVar _ -> ()
    | EApp e1 e2 ->
      src_refinements_are_closed_core n e1 x;
      src_refinements_are_closed_core n e2 x
    | EIf b e1 e2 ->
      src_refinements_are_closed_core n b x;    
      src_refinements_are_closed_core n e1 x;
      src_refinements_are_closed_core n e2 x    
    | ELam t e1 ->
      src_types_are_closed_core t x n;
      src_refinements_are_closed_core (n + 1) e1 x          
and src_types_are_closed_core (ty:s_ty) (x:RT.open_or_close) (n:nat)
  : Lemma (ensures RT.open_or_close_term' (elab_ty ty) x n == elab_ty ty)
          (decreases ty)
  = match ty with
    | TBool -> ()
    | TArrow t1 t2 ->
      src_types_are_closed_core t1 x n;
      src_types_are_closed_core t2 x (n + 1)
    | TRefineBool e ->
      assert (ln e);
      assert (closed e);
      ln_weaker e (-1) n;
      src_refinements_are_closed_core (n + 1) e x 

let src_refinements_are_closed (e:src_exp {ln e && closed e}) 
                               (x:RT.open_or_close)
  : Lemma (ensures RT.open_or_close_term' (elab_exp e) x 0 == elab_exp e)
          (decreases e)
 =  ln_weaker e (-1) 0;
    src_refinements_are_closed_core 0 e x 
 

#push-options "--query_stats --fuel 8 --ifuel 2 --z3rlimit_factor 2"
let rec elab_open_commute' (n:nat) (e:src_exp { ln' e n }) (x:var) 
  : Lemma (ensures
              RT.open_or_close_term' (elab_exp e) (RT.OpenWith (RT.var_as_term x)) n ==
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
      elab_open_commute' n e2 x;
      let opening = RT.OpenWith (RT.var_as_term x) in
      assert (RT.open_or_close_term' (elab_exp e) opening n ==
              R.(pack_ln (Tv_Match (RT.open_or_close_term' (elab_exp b) opening n)
                                  None
                                  [(Pat_Constant C_True, RT.open_or_close_term' (elab_exp e1) opening n);
                                   (Pat_Constant C_False, RT.open_or_close_term' (elab_exp e2) opening n)])))
    | ELam t e ->
      calc (==) {
        elab_exp (open_exp' (ELam t e) x n);
      (==) {}
        elab_exp (ELam t (open_exp' e x (n + 1)));      
      (==) {  }
        R.(pack_ln (Tv_Abs (RT.as_binder 0 (elab_ty t)) (elab_exp (open_exp' e x (n + 1)))));
      (==) { elab_open_commute' (n + 1) e x } 
        R.(pack_ln (Tv_Abs (RT.as_binder 0 (elab_ty t))
                           (RT.open_or_close_term' (elab_exp e) RT.(OpenWith (var_as_term x)) (n + 1))));
      (==) { src_types_are_closed_core t (RT.OpenWith (RT.var_as_term x)) n }
        RT.open_or_close_term'
          R.(pack_ln (Tv_Abs (RT.as_binder 0 (elab_ty t)) (elab_exp e)))
          RT.(OpenWith (var_as_term x))           
          n;
      }
#pop-options

let elab_open_commute (e:src_exp { ln' e 0 }) (x:var)
  : Lemma (RT.open_term (elab_exp e) x == elab_exp (open_exp e x))
          [SMTPat (RT.open_term (elab_exp e) x)]
  = elab_open_commute' 0 e x;
    RT.open_term_spec (elab_exp e) x

//key lemma about src types
let src_types_are_closed1 (ty:s_ty) (v:R.term)
  : Lemma (RT.open_with (elab_ty ty) v == elab_ty ty)
          [SMTPat (RT.open_with (elab_ty ty) v)]
  = src_types_are_closed_core ty (RT.OpenWith v) 0;
    RT.open_with_spec (elab_ty ty) v

let src_types_are_closed2 (ty:s_ty) (x:R.var)
  : Lemma (RT.close_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.close_term (elab_ty ty) x)]
  = src_types_are_closed_core ty (RT.CloseVar x) 0;
    RT.close_term_spec (elab_ty ty) x

let src_types_are_closed3 (ty:s_ty) (x:R.var)
  : Lemma (RT.open_term (elab_ty ty) x == elab_ty ty)
          [SMTPat (RT.open_term (elab_ty ty) x)]
  = src_types_are_closed_core ty (RT.OpenWith (RT.var_as_term x)) 0;
    RT.open_term_spec (elab_ty ty) x

let b2t_typing (g:fstar_env) (t:R.term) (dt:RT.typing g t RT.bool_ty)
  : RT.typing g (r_b2t t) RT.tm_type
  = let b2t_typing : RT.typing g _ b2t_ty = RT.T_FVar g b2t_fv in
    let app_ty : _ = RT.T_App _ _ _ _ _ b2t_typing dt in
    RT.open_with_spec RT.tm_type t;
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

open FStar.List.Tot    
let rec src_ty_ok_weakening (#f:fstar_top_env)
                            (sg sg':src_env)
                            (x:var { None? (lookup sg x) && None? (lookup sg' x) })
                            (b:binding)
                            (t:s_ty)
                            (d:src_ty_ok f (sg'@sg) t)
  : GTot (d':src_ty_ok f (sg'@((x, b)::sg)) t { t_height d' == t_height d })
         (decreases d)
  = match d with
    | OK_TBool _ -> OK_TBool _
    | OK_TArrow _ _ _ d1 d2 -> 
      let d1 = src_ty_ok_weakening _ _ _ _ _ d1 in
      let d2 = src_ty_ok_weakening _ _ _ _ _ d2 in      
      OK_TArrow _ _ _ d1 d2
    | OK_TRefine _ _ d -> OK_TRefine _ _ d

let rec rename (e:src_exp) (x y:var) 
  : e':src_exp { forall m. ln' e m ==> ln' e' m }
  = match e with
    | EBool _ -> e
    | EBVar _ -> e
    | EVar m -> if m = x then EVar y else EVar m
    | EIf b e1 e2 -> EIf (rename b x y) (rename e1 x y) (rename e2 x y)
    | ELam t e -> ELam t (rename e x y)
    | EApp e1 e2 -> EApp (rename e1 x y) (rename e2 x y)

let rename_binding (b:binding) (x y:var)
  : either s_ty src_eqn
  = match b with
    | Inl t -> Inl t
    | Inr (e1, e2) -> Inr (rename e1 x y, rename e2 x y)

let rename_src_env_elt (x y:var) (e : (var & either s_ty src_eqn))
  = let (a, b) = e in
    a, rename_binding b x y
    
let rename_env (sg:src_env) (x y:var)
  : src_env
  = L.map (rename_src_env_elt x y) sg

let rec rename_freevars (e:src_exp) (x y:var)
  : Lemma (freevars (rename e x y) `Set.subset` (freevars e `Set.union` (Set.singleton y)))
          [SMTPat (freevars (rename e x y))]
  = match e with
    | EBool _
    | EBVar _ 
    | EVar _ -> ()
    | EApp e1 e2 -> 
      rename_freevars e1 x y;
      rename_freevars e2 x y
    | EIf b e1 e2 ->
      rename_freevars b x y;    
      rename_freevars e1 x y;
      rename_freevars e2 x y    
    | ELam t body ->
      rename_freevars body x y        

let rec lookup_middle (sg sg':src_env)
                      (x:var { None? (lookup sg' x) })
                      (b:binding)
  : Lemma 
    (ensures lookup (sg'@(x,b)::sg) x == Some b)
    (decreases sg')
  = match sg' with
    | [] -> ()
    | hd::tl ->
      lookup_middle sg tl x b

let rec lookup_append_inverse (sg sg':src_env)
                              (z:var)
  : Lemma 
    (ensures (match lookup (sg'@sg) z with
              | None -> None? (lookup sg' z) && None? (lookup sg z)
              | Some b -> (lookup sg' z == Some b) \/
                         (None? (lookup sg' z) /\ lookup sg z == Some b)))
    (decreases sg')
  = match sg' with
    | [] -> ()
    | hd::tl -> lookup_append_inverse sg tl z

let cons_append_assoc (sg sg':list 'a) (x:'a)
  : Lemma (x::(sg'@sg) == (x::sg')@sg)
  = ()

let rec rename_open' (x y:var) 
                     (e:src_exp { ~ (x `Set.mem` freevars e) })
                     (n:nat)
  : Lemma 
    (ensures rename (open_exp' e x n) x y == open_exp' e y n)
    (decreases e)
  = match e with
    | EBool _ -> ()
    | EVar _ -> ()
    | EBVar _ -> ()
    | EApp e1 e2 -> 
      rename_open' x y e1 n;
      rename_open' x y e2 n    
    | EIf b e1 e2 ->
      rename_open' x y b n;    
      rename_open' x y e1 n;
      rename_open' x y e2 n         
    | ELam t e ->
      rename_open' x y e (n + 1)

let rec rename_id (x y:var) 
                  (e:src_exp { ~ (x `Set.mem` freevars e) \/ x == y })
  : Lemma 
    (ensures rename e x y == e)
    (decreases e)
  = match e with
    | EBool _ -> ()
    | EVar _ -> ()
    | EBVar _ -> ()
    | EApp e1 e2 -> 
      rename_id x y e1;
      rename_id x y e2      
    | EIf b e1 e2 ->
      rename_id x y b;    
      rename_id x y e1;
      rename_id x y e2      
    | ELam t e ->
      rename_id x y e

// This is a key lemma in renaming
// The precondition on `x` necessitates a a lot more reasoning on 
// freevars, freshness etc
let rename_open (e:src_exp) (x:var { ~(x `Set.mem` freevars e) }) (y:var)
  : Lemma (rename (open_exp e x) x y == open_exp e y)
  = rename_open' x y e 0

let rename_trivial (e:src_exp) (x:var) 
  : Lemma (rename e x x == e)
          [SMTPat (rename e x x)]
  = rename_id x x e 

let rec rename_open_commute' (e:src_exp) (z:var) (x y:var) (n:nat)
  : Lemma
    (requires z <> x /\ z <> y)
    (ensures rename (open_exp' e z n) x y == open_exp' (rename e x y) z n)
    (decreases e)
  = match e with
    | EBool _ -> ()
    | EVar _ -> ()
    | EBVar _ -> ()
    | EApp e1 e2 -> 
      rename_open_commute' e1 z x y n;
      rename_open_commute' e2 z x y n
    | EIf b e1 e2 ->
      rename_open_commute' b z x y n;    
      rename_open_commute' e1 z x y n;
      rename_open_commute' e2 z x y n
    | ELam t e ->
      rename_open_commute' e z x y (n + 1)

let rename_open_commute (e:src_exp) (z:var) (x y:var)
  : Lemma
    (requires z <> x /\ z <> y)
    (ensures rename (open_exp e z) x y == open_exp (rename e x y) z)
  = rename_open_commute' e z x y 0

let rec rename_lookup (sg:src_env) (a:var) (x y:var)
  : Lemma
    (ensures (
      match lookup sg a with
      | None -> None? (lookup (rename_env sg x y) a)
      | Some (Inl t) -> lookup (rename_env sg x y) a == Some (Inl t)
      | Some (Inr (e1, e2)) -> lookup (rename_env sg x y) a == Some (Inr (rename e1 x y, rename e2 x y))))
    (decreases sg)
    [SMTPat (lookup (rename_env sg x y) a)]
  = match sg with
    | [] -> ()
    | hd::tl -> rename_lookup tl a x y

let rec src_ty_ok_renaming (#f:fstar_top_env)
                           (sg sg':src_env)
                           (x:var { None? (lookup sg x) /\ None? (lookup sg' x) })
                           (y:var { None? (lookup sg y) /\ None? (lookup sg' x) })
                           (b:binding)
                           (t:s_ty)
                           (d:src_ty_ok f (sg'@(x,b)::sg) t)
  : GTot (d':src_ty_ok f (rename_env sg' x y@(y,b)::sg) t { t_height d' == t_height d })
         (decreases d)
  = match d with
    | OK_TBool _ -> OK_TBool _
    | OK_TArrow g t t' d1 d2 ->
      let d1 = src_ty_ok_renaming sg sg' x y _ _ d1 in
      let d2 = src_ty_ok_renaming sg sg' x y _ _ d2 in
      OK_TArrow _ _ _ d1 d2
    | OK_TRefine _ _ d -> OK_TRefine _ _ d

let as_bindings_append (sg0 sg1:src_env)
  : Lemma (as_bindings (sg0@sg1) == as_bindings sg0 @ as_bindings sg1)
  = L.map_append (fun (x, b) -> x, elab_binding b) sg0 sg1

let comp (f:'b -> 'c) (g:'a -> 'b) : 'a -> 'c = fun x -> f (g x)

let rec map_fusion (f:'b -> 'c) (g:'a -> 'b) (x:list 'a)
  : Lemma (L.map f (L.map g x) == L.map (comp f g) x)
  = match x with
    | [] -> ()
    | hd::tl -> map_fusion f g tl

let rec as_bindings_rename_env_append (sg sg':src_env) (x y:var)
  : Lemma 
    (ensures
           as_bindings (rename_env (sg@sg') x y) ==
           as_bindings (rename_env sg x y) @ as_bindings (rename_env sg' x y))
    (decreases sg)
  = match sg with
    | [] -> ()
    | hd::tl -> as_bindings_rename_env_append tl sg' x y
#push-options "--query_stats --fuel 8 --ifuel 4 --z3rlimit_factor 10"
let rec rename_elab_commute_core (m:int) (e:src_exp { ln' e m } ) (x y:var) (n:nat)
  : Lemma 
    (ensures RT.open_or_close_term' (elab_exp e) (RT.Rename x y) n ==
             elab_exp (rename e x y))
    (decreases e)
  = match e with
    | EBool _ -> ()
    | EBVar _ -> ()
    | EVar _ -> ()
    | EApp e0 e1 ->
      rename_elab_commute_core m e0 x y n;
      rename_elab_commute_core m e1 x y n
    | EIf b e0 e1 ->
      rename_elab_commute_core m b x y n;    
      rename_elab_commute_core m e0 x y n;
      rename_elab_commute_core m e1 x y n
    | ELam t e ->
      src_types_are_closed_core t (RT.Rename x y) n;
      rename_elab_commute_core (m + 1) e x y (n + 1)
#pop-options    
let rename_elab_commute (e:s_exp) (x y:var)
  : Lemma (RT.rename (elab_exp e) x y ==
           elab_exp (rename e x y))
  = rename_elab_commute_core (-1) e x y 0;
    RT.rename_spec (elab_exp e) x y

let rename_eq2 (t e0 e1: R.term) (x y:var)
  : Lemma (RT.rename (RT.eq2 t e0 e1) x y ==
           RT.eq2 (RT.rename t x y) (RT.rename e0 x y) (RT.rename e1 x y))
  = RT.rename_spec (RT.eq2 t e0 e1) x y;
    RT.rename_spec t x y;
    RT.rename_spec e0 x y;
    RT.rename_spec e1 x y

let rename_as_bindings_commute_1 (b:either s_ty src_eqn) (x y:var)
  : Lemma 
    (ensures 
      RT.rename (elab_binding b) x y ==
      elab_binding (rename_binding b x y))
  = match b with
    | Inl t ->
      assert (rename_binding b x y == Inl t);
      src_types_are_closed_core t (RT.Rename x y) 0;
      RT.rename_spec (elab_ty t) x y
    | Inr (e0, e1) -> 
      calc (==) {
        elab_binding (rename_binding b x y);
      (==) {}
       RT.eq2 RT.bool_ty 
              (elab_exp (rename e0 x y))
              (elab_exp (rename e1 x y));
      (==) {
              rename_elab_commute e0 x y;
              rename_elab_commute e1 x y
           }
      RT.eq2 RT.bool_ty 
              (RT.rename (elab_exp e0) x y)
              (RT.rename (elab_exp e1) x y);
      (==) { 
             rename_eq2 RT.bool_ty (elab_exp e0) (elab_exp e1) x y;
             RT.rename_spec RT.bool_ty x y
           }
      RT.rename (RT.eq2 RT.bool_ty (elab_exp e0) (elab_exp e1)) x y;
      }

let rec rename_as_bindings_commute (sg:src_env) (x y:var)
  : Lemma 
    (ensures 
      as_bindings (rename_env sg x y) ==
      RT.rename_bindings (as_bindings sg) x y)
    (decreases sg)
  = match sg with
    | [] -> ()
    | (z,b)::tl ->
      calc (==)  {
        as_bindings (rename_env sg x y);
      (==) { as_bindings_rename_env_append [(z,b)] tl x y }
        (z, elab_binding (rename_binding b x y)) :: as_bindings (rename_env tl x y);
      (==) {  rename_as_bindings_commute tl x y }
        (z, elab_binding (rename_binding b x y)) :: RT.rename_bindings (as_bindings tl) x y;
      (==) { rename_as_bindings_commute_1 b x y }
        (z, RT.rename (elab_binding b) x y) :: RT.rename_bindings (as_bindings tl) x y;      
      (==) { }
        RT.rename_bindings (as_bindings sg) x y;
      }
          
let core_subtyping_renaming
                        (#f:fstar_top_env)
                        (sg sg':src_env)
                        (x:var { None? (lookup sg x) && None? (lookup sg' x) })
                        (y:var { None? (lookup sg y) && None? (lookup sg' y) })
                        (b:binding)
                        (t0 t1:s_ty)
                        (d:RT.sub_typing (extend_env_l f (sg'@(x,b)::sg)) (elab_ty t0) (elab_ty t1))
  : GTot (RT.sub_typing (extend_env_l f (rename_env sg' x y@(y,b)::sg)) (elab_ty t0) (elab_ty t1))
  = match d with
    | RT.ST_Refl _ _ -> RT.ST_Refl _ _
    | RT.ST_Token _ _ _ tok ->
      calc (==) {
        extend_env_l f (sg'@(x,b)::sg);
      (==) { extend_env_equiv f (sg'@(x,b)::sg) }
        RT.extend_env_l f (as_bindings (sg'@(x,b)::sg));
      (==) { as_bindings_append sg' ((x,b)::sg) }
        RT.extend_env_l f ((as_bindings sg')@(x, elab_binding b)::as_bindings sg);      
      };
      let tok : RT.subtyping_token (RT.extend_env_l f ((as_bindings sg')@(x, elab_binding b)::as_bindings sg))
                                   (elab_ty t0)
                                   (elab_ty t1)
            = tok in
      extend_env_equiv f (sg'@sg);
      as_bindings_append sg' sg;
      extend_env_l_lookup_bvar f (sg'@sg) x;
      extend_env_l_lookup_bvar f (sg'@sg) y;
      lookup_append_inverse sg sg' x;
      lookup_append_inverse sg sg' y;      
      assert (None? (RT.lookup_bvar (RT.extend_env_l f ((as_bindings sg')@as_bindings sg)) x));
      assert (None? (RT.lookup_bvar (RT.extend_env_l f ((as_bindings sg')@as_bindings sg)) y));      
      let tok : RT.subtyping_token
                    (RT.extend_env_l f (RT.rename_bindings (as_bindings sg') x y@(y, elab_binding b)::as_bindings sg))
                    (RT.rename (elab_ty t0) x y)
                    (RT.rename (elab_ty t1) x y)                    
          = RT.subtyping_token_renaming f _ _ _ y _ _ _ tok in
      RT.rename_spec (elab_ty t0) x y; 
      RT.rename_spec (elab_ty t1) x y;       
      src_types_are_closed_core t0 (RT.Rename x y) 0;
      src_types_are_closed_core t1 (RT.Rename x y) 0;      
      let tok : RT.subtyping_token
                    (RT.extend_env_l f (RT.rename_bindings (as_bindings sg') x y@(y, elab_binding b)::as_bindings sg))
                    (elab_ty t0)
                    (elab_ty t1)
          = tok in
      rename_as_bindings_commute sg' x y;
      assert (RT.rename_bindings (as_bindings sg') x y ==
              as_bindings (rename_env sg' x y));
      let tok : RT.subtyping_token
                    (RT.extend_env_l f (as_bindings (rename_env sg' x y)@(y, elab_binding b)::as_bindings sg))
                    (elab_ty t0)
                    (elab_ty t1)
              = tok
      in
      extend_env_equiv f ((rename_env sg' x y)@(y,b)::sg);
      calc (==) {
        RT.extend_env_l f (as_bindings (rename_env sg' x y)@(y, elab_binding b)::as_bindings sg);
      (==) {  as_bindings_append (rename_env sg' x y) ((y,b)::sg) }
        RT.extend_env_l f (as_bindings (rename_env sg' x y@(y, b)::sg));      
      (==) {extend_env_equiv f ((rename_env sg' x y)@(y,b)::sg) }
        extend_env_l f ((rename_env sg' x y)@(y, b)::sg);      
      };
      let tok : RT.subtyping_token
                    (extend_env_l f ((rename_env sg' x y)@(y, b)::sg))
                    (elab_ty t0)
                    (elab_ty t1)
              = tok
      in
      RT.ST_Token _ _ _ tok

                        
let sub_typing_renaming (#f:fstar_top_env)
                        (sg sg':src_env)
                        (x:var { None? (lookup sg x) && None? (lookup sg' x) })
                        (y:var { None? (lookup sg y) && None? (lookup sg' y) })
                        (b:binding)
                        (t0 t1:s_ty)
                        (d:sub_typing f (sg'@(x,b)::sg) t0 t1)
  : GTot (d':sub_typing f (rename_env sg' x y@(y,b)::sg) t0 t1 { s_height d' == s_height d })
         (decreases (s_height d))
  = match d with
    | S_Refl _ _ -> S_Refl _ _ 
    | S_ELab g _ _ d ->
      S_ELab _ _ _ (core_subtyping_renaming sg sg' x y b t0 t1 d)


#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 2"
let freevars_included_in (e:src_exp) (sg:src_env) =
  forall x. x `Set.mem` freevars e ==> Some? (lookup sg x)
  
let rec src_typing_freevars #f (sg:src_env) (e:src_exp) (t:s_ty) (d:src_typing f sg e t)
  : Lemma 
    (ensures e `freevars_included_in` sg)
    (decreases d)
  = match d with
    | T_Bool _ _ -> ()
    | T_Var _ _ -> ()
    | T_App _ _ _ _ _ _ d1 d2 s ->
      src_typing_freevars _ _ _ d1;
      src_typing_freevars _ _ _ d2      
    | T_If _ _ _ _ _ _ _ hyp db d1 d2 s1 s2 ->
      src_typing_freevars _ _ _ db;
      src_typing_freevars _ _ _ d1;
      src_typing_freevars _ _ _ d2      
    | T_Lam _ _ _ _ x dt dbody ->
      src_typing_freevars _ _ _ dbody
  
#push-options "--z3rlimit_factor 4"
let rec src_typing_renaming (#f:fstar_top_env)
                            (sg sg':src_env)
                            (x:var { None? (lookup sg x) && None? (lookup sg' x) })
                            (y:var { None? (lookup sg y) && None? (lookup sg' y) })
                            (b:binding)
                            (e:src_exp)
                            (t:s_ty)
                            (d:src_typing f (sg'@(x,b)::sg) e t)
  : GTot (d':src_typing f (rename_env sg' x y@(y,b)::sg) (rename e x y) t { height d' == height d })
         (decreases (height d))
  = let aux (z:var { None? (lookup (sg'@(x,b)::sg) z) })
            (b':binding)
            (e:src_exp)
            (t:s_ty)
            (ds:src_typing f ((z, b')::sg'@(x,b)::sg) e t { height ds < height d })
      : GTot (
          zz:var {
                   None? (lookup (rename_env sg' x y@(y,b)::sg) zz) /\
                   (zz <> z ==> ~(zz `Set.mem` freevars e)) /\
                   zz <> x /\
                   zz <> y /\
                   zz == fresh ((y,b)::sg'@(x,b)::sg)
                 } &
          ds':src_typing f (rename_env ((zz,b')::sg') x y@(y,b)::sg) (rename (rename e z zz) x y) t { height ds == height ds' }
        )
      = //pick a new opening variable zz
        //that is fresh for both x and y (and sg, sg')
        src_typing_freevars  _ _ _ ds;
        assert (freevars_included_in e (((z, b')::sg'@(x,b)::sg)));
        let zz = fresh ((y,b)::sg'@(x,b)::sg) in
        fresh_is_fresh ((y,b)::sg'@(x,b)::sg);
        lookup_append_inverse ((x,b)::sg) ((y,b)::sg') zz;
        //first use the renaming lemma to rewrite the original derivation to replace z with zz
        let ds : src_typing f ((zz, b')::(sg'@(x,b)::sg)) (rename e z zz) t
          = src_typing_renaming _ [] z zz b' _ _ ds
        in
        lookup_append_inverse ((y,b)::sg) (rename_env sg' x y) zz;
        //then use the renaming lemma again t rewrite the variable in the middle, replacing x with y
        let ds
          : src_typing f (rename_env ((zz, b')::sg') x y@(y,b)::sg) (rename (rename e z zz) x y) t
          = src_typing_renaming sg ((zz, b')::sg') x y b _ _ ds
        in
        assert (zz <> z ==> ~(zz `Set.mem` freevars e));
        (| zz, ds |)
    in
    match d with
    | T_Bool _ b ->
      T_Bool _ b

    | T_Var _ z -> 
       if z = x
       then (
         lookup_middle sg sg' x b;
         lookup_middle sg (rename_env sg' x y) y b;         
         T_Var _ y
       )
       else (
         lookup_append_inverse ((x,b)::sg) sg' z;
         lookup_append_inverse ((y,b)::sg) (rename_env sg' x y) z;
         T_Var _ z
       )


    | T_App _ e1 e2 t t' t0 d1 d2 st ->
      let d1 = src_typing_renaming sg sg' x y b _ _ d1 in
      let d2 = src_typing_renaming sg sg' x y b _ _ d2 in
      let st = sub_typing_renaming sg sg' x y b _ _ st in
      T_App _ _ _ _ _ _ d1 d2 st

    | T_Lam g t body t' z dt dbody ->
      let (| zz, dbody |) = aux z (Inl t) _ _  dbody in
      rename_open body z zz;      
      rename_open_commute body zz x y;
      let dbody
        : src_typing f (rename_env ((zz, Inl t)::sg') x y@(y,b)::sg) (open_exp (rename body x y) zz) t'
        = dbody
      in
      let dt
        : src_ty_ok f (rename_env sg' x y@(y,b)::sg) t
        = src_ty_ok_renaming sg sg' x y b _ dt
      in
      rename_freevars body x y;
      T_Lam _ t _ _ zz dt dbody

    | T_If g eb e1 e2 t1 t2 t hyp db dt1 dt2 st1 st2 ->
      let db = src_typing_renaming sg sg' x y b _ _ db in
      let (| hyp', dt1 |) = aux hyp (Inr (eb , EBool true)) _ _ dt1 in
      let (| hyp'', dt2 |) = aux hyp (Inr (eb, EBool false)) _ _ dt2 in      
      let dt1 : src_typing _ _ (rename (rename e1 hyp hyp') x y) t1 = dt1 in
      rename_id hyp hyp' e1;
      rename_id hyp hyp' e2;      
      assert (hyp' == hyp'');
      fresh_is_fresh ((y,b)::sg'@(x,b)::sg);
      lookup_append_inverse ((x,b)::sg) ((y,b)::sg') hyp;
      let st1 
        : sub_typing f ((hyp', Inr (eb, EBool true))::g) t1 t
        = sub_typing_renaming g [] hyp hyp' (Inr (eb, EBool true)) _ _ st1
      in
      let st1
        : sub_typing f ((hyp', Inr (rename eb x y, EBool true))::(rename_env sg' x y)@(y,b)::sg) t1 t
        = sub_typing_renaming sg ((hyp', Inr (eb, EBool true))::sg') x y b _ _ st1
      in
      let st2
        : sub_typing f ((hyp', Inr (eb, EBool false))::g) t2 t
        = sub_typing_renaming g [] hyp hyp' (Inr (eb, EBool false)) _ _ st2
      in
      let st2
        : sub_typing f ((hyp', Inr (rename eb x y, EBool false))::(rename_env sg' x y)@(y,b)::sg) t2 t
        = sub_typing_renaming sg ((hyp', Inr (eb, EBool false))::sg') x y b _ _ st2
      in 
      T_If _ _ _ _ _ _ _ _ db dt1 dt2 st1 st2

let sub_typing_weakening #f (sg sg':src_env) 
                         (x:var { None? (lookup sg x) && None? (lookup sg' x) })
                         (b:binding)
                         (t1 t2:s_ty)
                         (d:sub_typing f (sg'@sg) t1 t2)
  : GTot (d':sub_typing f (sg'@((x, b)::sg)) t1 t2 { s_height d == s_height d' })
         (decreases (s_height d))
  = match d with
    | S_Refl _ _  -> S_Refl _ _
    | S_ELab _ _ _ d -> 
      match d with
      | RT.ST_Refl _ _ ->
        let d : RT.sub_typing (extend_env_l f ((sg'@((x, b)::sg)))) (elab_ty t1) (elab_ty t2) = RT.ST_Refl _ _ in
        S_ELab _ _ _ d
        
      | RT.ST_Token _ _ _ tok ->
        let tok
          : RT.subtyping_token 
                      (extend_env_l f (sg'@sg))
                      (elab_ty t1)
                      (elab_ty t2)
          = tok
        in
        calc (==) {
          extend_env_l f (sg'@sg);
        (==) { extend_env_equiv f (sg'@sg) }
          RT.extend_env_l f (as_bindings (sg'@sg));
        (==) { as_bindings_append sg' sg }
          RT.extend_env_l f (as_bindings sg' @ as_bindings sg);
        };
        lookup_append_inverse sg sg' x;
        extend_env_l_lookup_bvar f (sg'@sg) x;
        let tok
          : RT.subtyping_token 
                      (RT.extend_env_l f (as_bindings sg'@(x, elab_binding b)::as_bindings sg))
                      (elab_ty t1)
                      (elab_ty t2)
          = RT.subtyping_token_weakening f (as_bindings sg) (as_bindings sg') x (elab_binding b) _ _ tok in
        calc (==) {
           RT.extend_env_l f (as_bindings sg'@(x, elab_binding b)::as_bindings sg);
        (==) { as_bindings_append sg' ((x,b)::sg) }
           RT.extend_env_l f (as_bindings (sg'@(x, b)::sg));
        (==) { extend_env_equiv f (sg'@(x,b)::sg) }
           extend_env_l f (sg'@(x, b)::sg);        
        };
        let tok
          : RT.subtyping_token 
                      (extend_env_l f (sg'@(x,b)::sg))
                      (elab_ty t1)
                      (elab_ty t2)
          = tok
        in
        let d : RT.sub_typing (extend_env_l f ((sg'@((x, b)::sg)))) (elab_ty t1) (elab_ty t2) 
          = RT.ST_Token _ _ _ tok
        in
        S_ELab _ _ _ d
        

let rec src_typing_weakening #f (sg sg':src_env) 
                             (x:var { None? (lookup sg x) && None? (lookup sg' x) })
                             (b:binding)
                             (e:src_exp)
                             (t:s_ty)                         
                             (d:src_typing f (sg'@sg) e t)
  : GTot (d':src_typing f (sg'@((x, b)::sg)) e t { height d == height d' })
         (decreases (height d))
  = match d with
    | T_Bool _ b -> T_Bool _ b

    | T_Var _ y -> 
      lookup_append_inverse sg sg' y;      
      lookup_append_inverse ((x,b)::sg) sg' y;
      T_Var _ y

    | T_App g e1 e2 t t' s0 d1 d2 s ->
      let d1 = src_typing_weakening _ _ _ _ _ _ d1 in
      let d2 = src_typing_weakening _ _ _ _ _ _ d2 in      
      let s = sub_typing_weakening _ _ _ _ _ _ s in
      T_App _ _ _ _ _ _ d1 d2 s

    | T_Lam g t e t' y dt de ->
      assert (None? (lookup (sg'@sg) y));
      lookup_append_inverse sg sg' y;
      src_typing_freevars _ _ _ d;
      let dt = src_ty_ok_weakening sg sg' x b _ dt in
      let y' = fresh (sg'@((x,b) :: sg)) in
      fresh_is_fresh (sg'@((x,b) :: sg));
      lookup_append_inverse ((x,b)::sg) sg' y';
      lookup_append_inverse sg sg' y';      
      assert (None? (lookup (sg'@sg) y'));
      let de 
        : src_typing f ((y', Inl t)::(sg'@sg)) (open_exp e y') t'
        = rename_open e y y';
          src_typing_renaming (sg'@sg) [] y y' (Inl t) _ _ de
      in
      let de
        : src_typing f ((y', Inl t)::sg'@(x,b)::sg) (open_exp e y') t'
        = src_typing_weakening sg ((y', Inl t)::sg') x b _ _ de
      in
      T_Lam _ _ _ _ _ dt de

    | T_If g eb e1 e2 t1 t2 t hyp db d1 d2 s1 s2 ->
      src_typing_freevars _ _ _ d;
      let db = src_typing_weakening _ _ _ _ _ _ db in
      lookup_append_inverse sg sg' hyp;
      let hyp' = fresh (sg'@((x,b) :: sg)) in
      fresh_is_fresh (sg'@((x,b) :: sg));
      lookup_append_inverse ((x,b)::sg) sg' hyp';
      lookup_append_inverse sg sg' hyp';      
      rename_id hyp hyp' e1;
      rename_id hyp hyp' e2;      
      let d1 
        : src_typing f ((hyp', Inr (eb, EBool true))::(sg'@sg)) (rename e1 hyp hyp') t1
        = src_typing_renaming (sg'@sg) [] hyp hyp' _ _ _ d1
      in
      let d1
        : src_typing f ((hyp', Inr (eb, EBool true))::sg'@(x,b)::sg) (rename e1 hyp hyp') t1
        = src_typing_weakening sg ((hyp', Inr (eb, EBool true))::sg') x b _ _ d1
      in
      let d2
        : src_typing f ((hyp', Inr (eb, EBool false))::(sg'@sg)) (rename e2 hyp hyp') t2
        = src_typing_renaming (sg'@sg) [] hyp hyp' _ _ _ d2
      in
      let d2
        : src_typing f ((hyp', Inr (eb, EBool false))::sg'@(x,b)::sg) (rename e2 hyp hyp') t2
        = src_typing_weakening sg ((hyp', Inr (eb, EBool false))::sg') x b _ _ d2
      in
      let s1 : sub_typing f ((hyp', Inr (eb, EBool true))::sg'@(x,b)::sg) t1 t
         = sub_typing_weakening sg ((hyp', Inr (eb, EBool true))::sg') x b _ _
                                   (sub_typing_renaming g [] hyp hyp' _ _ _ s1)
      in
      let s2 : sub_typing f ((hyp', Inr (eb, EBool false))::sg'@(x,b)::sg) t2 t
         = sub_typing_weakening sg ((hyp', Inr (eb, EBool false))::sg') x b _ _
                                   (sub_typing_renaming g [] hyp hyp' _ _ _ s2)
      in      
      T_If _ _ _ _ _ _ _ hyp' db d1 d2 s1 s2
                         
let rec src_typing_weakening_l #f (sg:src_env) 
                               (sg':src_env { 
                                 (src_env_ok sg') /\
                                 (forall x. Some? (lookup sg' x) ==> None? (lookup sg x))
                               })
                           (e:src_exp)
                           (t:s_ty)                         
                           (d:src_typing f sg e t)
  : GTot (d':src_typing f L.(sg' @ sg) e t { height d == height d' })
         (decreases sg')
  = match sg' with
    | [] -> d
    | (x, b)::tl ->
      let d = src_typing_weakening_l sg tl e t d in
      lookup_append_inverse sg tl x;
      src_typing_weakening (tl@sg) [] x b _ _ d

let open_with_fvar_id (fv:R.fv) (x:R.term)
  : Lemma (RT.open_with (R.pack_ln (R.Tv_FVar fv)) x == (R.pack_ln (R.Tv_FVar fv)))
          [SMTPat (RT.open_with (R.pack_ln (R.Tv_FVar fv)) x)]
  = RT.open_with_spec (R.pack_ln (R.Tv_FVar fv)) x

let open_term_fvar_id (fv:R.fv) (x:var)
  : Lemma (RT.open_term (R.pack_ln (R.Tv_FVar fv)) x == (R.pack_ln (R.Tv_FVar fv)))
          [SMTPat (RT.open_term (R.pack_ln (R.Tv_FVar fv)) x)]
  = RT.open_term_spec (R.pack_ln (R.Tv_FVar fv)) x

let subtyping_soundness #f (#sg:src_env) (#t0 #t1:s_ty) (ds:sub_typing f sg t0 t1)
  : GTot (RT.sub_typing (extend_env_l f sg) (elab_ty t0) (elab_ty t1))
  = match ds with
    | S_Refl _ _ -> RT.ST_Refl _ _
    | S_ELab _ _ _ d -> d

let bv0 = R.pack_bv (RT.make_bv 0 RT.bool_ty)

let bv_as_arg (x:R.bv)
  = let open R in
    pack_ln (Tv_BVar x), Q_Explicit

let var_as_arg (x:R.bv)
  = let open R in
    pack_ln (Tv_Var x), Q_Explicit

let apply (e:R.term) (x:_)
  : R.term
  = let open R in
    pack_ln (Tv_App e x) 

let mk_refine (e:R.term)
  : R.term 
  = let open R in
    let ref = apply e (bv_as_arg bv0) in
    pack_ln (Tv_Refine bv0 (r_b2t ref))

#push-options "--fuel 4"
let apply_refinement_closed (e:src_exp { ln e && closed e })
                            (x:var)
  : Lemma (RT.open_term (r_b2t (apply (elab_exp e) (bv_as_arg bv0))) x
           ==
           r_b2t (apply (elab_exp e) (RT.var_as_term x, R.Q_Explicit)))
  = RT.open_term_spec (r_b2t (apply (elab_exp e) (bv_as_arg bv0))) x;
    src_refinements_are_closed_core 0 e (RT.OpenWith (RT.var_as_term x))
#pop-options

let rec soundness (#f:fstar_top_env)
                  (#sg:src_env { src_env_ok sg } ) 
                  (#se:src_exp { ln se })
                  (#st:s_ty)
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
      let dt : RT.typing (extend_env_l f sg) (elab_ty t) RT.tm_type =
        src_ty_ok_soundness sg t dt
      in
      let dd
        : RT.typing (extend_env_l f sg)
                    (R.pack_ln (R.Tv_Abs (RT.as_binder 0 (elab_ty t)) (elab_exp e)))
                    (elab_ty (TArrow t t'))
        = RT.T_Abs (extend_env_l f sg)
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

    | T_If _ b e1 e2 t1 t2 t hyp db d1 d2 s1 s2 ->
      let db = soundness db in
      let d1 = soundness d1 in
      let d2 = soundness d2 in
      let s1 = subtyping_soundness s1 in
      let s2 = subtyping_soundness s2 in
      let d1 = RT.T_Sub _ _ _ _ d1 s1 in
      let d2 = RT.T_Sub _ _ _ _ d2 s2 in      
      RT.T_If (extend_env_l f sg) (elab_exp b) (elab_exp e1) (elab_exp e2) _ hyp db d1 d2


and src_ty_ok_soundness (#f:fstar_top_env)
                        (sg:src_env { src_env_ok sg })
                        (t:s_ty)
                        (dt:src_ty_ok f sg t)
 : GTot (RT.typing (extend_env_l f sg) (elab_ty t) RT.tm_type)
        (decreases (t_height dt))
 = match dt with
   | OK_TBool _ ->
     RT.T_FVar _ RT.bool_fv
     
   | OK_TArrow _ t1 t2 ok_t1 ok_t2 ->
     let t1_ok = src_ty_ok_soundness sg _ ok_t1 in
     let x = fresh sg in
     fresh_is_fresh sg;
     let t2_ok = src_ty_ok_soundness ((x, Inl t1)::sg) _ (src_ty_ok_weakening _ [] _ _ _ ok_t2) in
     RT.T_Arrow _ x (elab_ty t1) (elab_ty t2) t1_ok t2_ok
     
   | OK_TRefine _ e de ->
     let x = fresh sg in
     fresh_is_fresh sg;
     let sg' = ((fresh sg, Inl TBool)::sg) in
     let de = src_typing_weakening_l [] sg' _ _ de in
     let de : RT.typing (RT.extend_env (extend_env_l f sg) x RT.bool_ty)
                        (elab_exp e)
                        (elab_ty (TArrow TBool TBool)) = soundness de in
     let arg_x = RT.var_as_term x in
     let arg_x_typing
       : RT.typing (RT.extend_env (extend_env_l f sg) x RT.bool_ty)
                   arg_x
                   RT.bool_ty
       = RT.T_Var _ (RT.var_as_bv x)
     in
     let refinement = apply (elab_exp e) (arg_x, R.Q_Explicit) in
     let dr : RT.typing (RT.extend_env (extend_env_l f sg) x RT.bool_ty)
                        refinement
                        RT.bool_ty
            = RT.T_App (RT.extend_env (extend_env_l f sg) x RT.bool_ty)
                       (elab_exp e)
                       (arg_x)
                       (RT.as_binder 0 RT.bool_ty)
                       RT.bool_ty
                       de
                       arg_x_typing
     in
     let dr : RT.typing (RT.extend_env (extend_env_l f sg) x RT.bool_ty)
                        (r_b2t refinement)
                        RT.tm_type
            = b2t_typing _ _ dr
     in
     apply_refinement_closed e x;
     let refinement' = r_b2t (apply (elab_exp e) (bv_as_arg bv0)) in
     assert (RT.open_term refinement' x == r_b2t refinement);
     let bool_typing
       : RT.typing (extend_env_l f sg) RT.bool_ty RT.tm_type 
       = RT.T_FVar _ RT.bool_fv
     in
     RT.T_Refine (extend_env_l f sg) x RT.bool_ty refinement' bool_typing dr

let soundness_lemma (f:fstar_top_env)
                    (sg:src_env { src_env_ok sg }) 
                    (se:src_exp { ln se })
                    (st:s_ty)
  : Lemma
    (requires src_typing f sg se st)
    (ensures  RT.typing (extend_env_l f sg)
                        (elab_exp se)
                        (elab_ty st))
  = FStar.Squash.bind_squash 
      #(src_typing f sg se st)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness dd))

let main (f:fstar_top_env)
         (src:src_exp)
  : T.Tac (e:R.term & t:R.term { RT.typing f e t })
  = if ln src && closed src
    then 
      let (| src_ty, _ |) = check f [] src in
      soundness_lemma f [] src src_ty;
      (| elab_exp src, elab_ty src_ty |)
    else T.fail "Not locally nameless"
