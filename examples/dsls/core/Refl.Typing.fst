module Refl.Typing
open FStar.List.Tot
open FStar.Reflection
module R = FStar.Reflection

let inspect_pack (t:R.term_view)
  : Lemma (ensures R.(inspect_ln (pack_ln t) == t))
          [SMTPat R.(inspect_ln (pack_ln t))]
  = R.inspect_pack_inv t
  
let pack_inspect (t:R.term)
  : Lemma (ensures R.(pack_ln (inspect_ln t) == t))
          [SMTPat R.(pack_ln (inspect_ln t))]
  = R.pack_inspect_inv t
  
let inspect_pack_bv (t:R.bv_view)
  : Lemma (ensures R.(inspect_bv (pack_bv t) == t))
          [SMTPat R.(inspect_bv (pack_bv t))]
  = admit()
  
let pack_inspect_bv (t:R.bv)
  : Lemma (ensures R.(pack_bv (inspect_bv t) == t))
          [SMTPat R.(pack_bv (inspect_bv t))]
  = admit()
  
let inspect_pack_binder (b:_) (q:_) (a:_)
  : Lemma (ensures R.(R.inspect_binder (R.pack_binder b q a) == (b, (q, a))))
          [SMTPat R.(inspect_binder (pack_binder b q a))]
  = admit()
  
let pack_inspect_binder (t:R.binder)
  : Lemma (ensures (let b, (q, a) = R.inspect_binder t in
                    R.(pack_binder b q a == t)))
  = admit()
  
let pack_inspect_comp (t:R.comp)
  : Lemma (ensures (R.pack_comp (R.inspect_comp t) == t))
          [SMTPat (R.pack_comp (R.inspect_comp t))]
  = R.pack_inspect_comp_inv t
  
let inspect_pack_comp (t:R.comp_view)
  : Lemma (ensures (R.inspect_comp (R.pack_comp t) == t))
          [SMTPat (R.inspect_comp (R.pack_comp t))]
  = R.inspect_pack_comp_inv t
  
assume
val lookup_bvar (e:env) (x:int) : option term

assume
val lookup_fvar_uinst (e:R.env) (x:R.fv) (us:list R.universe) : option R.term

let lookup_fvar (e:env) (x:fv) : option term = lookup_fvar_uinst e x []

assume
val extend_env (e:env) (x:var) (ty:term) : env

assume
val lookup_bvar_extend_env (g:env) (x y:var) (ty:term)
  : Lemma 
    (ensures (
           if x = y
           then lookup_bvar (extend_env g x ty) y == Some ty
           else lookup_bvar (extend_env g x ty) y == lookup_bvar g y))
    [SMTPat (lookup_bvar (extend_env g x ty) y)]

assume
val lookup_fvar_extend_env (g:env) (x:fv) (us:universes) (y:var) (ty:term)
  : Lemma 
    (ensures lookup_fvar_uinst (extend_env g y ty) x us == lookup_fvar_uinst g x us)
    [SMTPat (lookup_fvar_uinst (extend_env g y ty) x us)]

let mk_binder (pp_name:string) (x:var) (ty:term) (q:aqualv)
  = pack_binder
      (pack_bv ({bv_ppname=pp_name;
                 bv_index=x;
                 bv_sort=ty}))
      q
      []

let bv_index (x:bv) : int = (inspect_bv x).bv_index

let binder_sort (b:binder) =
  let bv, _ = inspect_binder b in 
  (inspect_bv bv).bv_sort

let binder_qual (b:binder) =
  let _, (q, _) = inspect_binder b in q


//replace BV 0 in t with v
noeq
type open_or_close =
  | OpenWith of term
  | OpenWithVar of var
  | CloseVar of var
  | Rename   : var -> var -> open_or_close

assume
val open_or_close_ctx_uvar_and_subst (c:ctx_uvar_and_subst) (v:open_or_close) (i:nat) 
  : ctx_uvar_and_subst

let rec binder_offset_patterns (ps:list (pattern & bool))
  : nat
  = match ps with
    | [] -> 0
    | (p, b)::ps ->
      let n = binder_offset_pattern p in
      let m = binder_offset_patterns ps in
      n + m

and binder_offset_pattern (p:pattern)
  : nat
  = match p with
    | Pat_Constant _
    | Pat_Dot_Term _ -> 0

    | Pat_Var _
    | Pat_Wild _ -> 1

    | Pat_Cons fv us pats -> 
      binder_offset_patterns pats

let rec open_or_close_term' (t:term) (v:open_or_close) (i:nat)
  : GTot term (decreases t)
  = match inspect_ln t with
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown -> t
    | Tv_Var x ->
      (match v with
       | OpenWith _ 
       | OpenWithVar _ -> t
       | CloseVar y ->
         if bv_index x = y 
         then pack_ln (Tv_BVar (pack_bv { inspect_bv x with bv_index = i }))
         else t
       | Rename y z ->
         if bv_index x = y
         then pack_ln (Tv_Var (pack_bv { inspect_bv x with bv_index = z }))
         else t)

    | Tv_BVar j -> 
      (match v with
       | Rename _ _ -> t
       | CloseVar _ -> t
       | OpenWith v ->
         if i=bv_index j 
         then v
         else t
       | OpenWithVar v ->
         if i = bv_index j
         then pack_ln (Tv_Var (pack_bv { inspect_bv j with bv_index = v }))
         else t)

    | Tv_App hd argv ->
      pack_ln (Tv_App (open_or_close_term' hd v i)
                      (open_or_close_term' (fst argv) v i, snd argv))

    | Tv_Abs b body -> 
      let b' = open_or_close_binder' b v i in
      pack_ln (Tv_Abs b' (open_or_close_term' body v (i + 1)))

    | Tv_Arrow b c ->
      let b' = open_or_close_binder' b v i in
      pack_ln (Tv_Arrow b' (open_or_close_comp' c v (i + 1)))      

    | Tv_Refine bv f ->
      let bv' = open_or_close_bv' bv v i in
      pack_ln (Tv_Refine bv' (open_or_close_term' f v (i + 1)))

    | Tv_Uvar j c ->
      pack_ln (Tv_Uvar j (open_or_close_ctx_uvar_and_subst c v i))
      
    | Tv_Let recf attrs bv def body ->
      pack_ln (Tv_Let recf 
                      (open_or_close_terms' attrs v i)
                      (open_or_close_bv' bv v i)
                      (if recf 
                       then open_or_close_term' def v (i + 1)
                       else open_or_close_term' def v i)
                      (open_or_close_term' body v (i + 1)))

    | Tv_Match scr ret brs ->
      pack_ln (Tv_Match (open_or_close_term' scr v i)
                        (match ret with
                         | None -> None
                         | Some m -> Some (open_or_close_match_returns' m v i))
                        (open_or_close_branches' brs v i))
      
    | Tv_AscribedT e t tac b ->
      pack_ln (Tv_AscribedT (open_or_close_term' e v i)
                            (open_or_close_term' t v i)
                            (match tac with
                             | None -> None
                             | Some tac -> Some (open_or_close_term' tac v i))
                             b)

    | Tv_AscribedC e c tac b ->
      pack_ln (Tv_AscribedC (open_or_close_term' e v i)
                            (open_or_close_comp' c v i)
                            (match tac with
                             | None -> None
                             | Some tac -> Some (open_or_close_term' tac v i))
                             b)

and open_or_close_bv' (b:bv) (v:open_or_close) (i:nat)
  : GTot bv (decreases b)
  = let bv = inspect_bv b in
    pack_bv ({bv with bv_sort = open_or_close_term' bv.bv_sort v i})

and open_or_close_binder' (b:binder) (v:open_or_close) (i:nat)
  : GTot binder (decreases b)
  = let bndr  = inspect_binder b in
    let bv, (q, attrs) = bndr in
    pack_binder (open_or_close_bv' bv v i) 
                q
                (open_or_close_terms' attrs v i)

and open_or_close_comp' (c:comp) (v:open_or_close) (i:nat)
  : GTot comp (decreases c)
  = match inspect_comp c with
    | C_Total t u decr ->
      pack_comp (C_Total (open_or_close_term' t v i) u
                         (open_or_close_terms' decr v i))

    | C_GTotal t u decr ->
      pack_comp (C_GTotal (open_or_close_term' t v i) u
                          (open_or_close_terms' decr v i))

    | C_Lemma pre post pats ->
      pack_comp (C_Lemma (open_or_close_term' pre v i)
                         (open_or_close_term' post v i)
                         (open_or_close_term' pats v i))

    | C_Eff us eff_name res args ->
      pack_comp (C_Eff us eff_name
                       (open_or_close_term' res v i)
                       (open_or_close_args' args v i))

and open_or_close_terms' (ts:list term) (v:open_or_close) (i:nat)
  : GTot (list term) (decreases ts)
  = match ts with
    | [] -> []
    | t::ts -> open_or_close_term' t v i :: open_or_close_terms' ts v i

and open_or_close_args' (ts:list argv) (v:open_or_close) (i:nat)
  : GTot (list argv) (decreases ts)
  = match ts with
    | [] -> []
    | (t,q)::ts -> (open_or_close_term' t v i,q) :: open_or_close_args' ts v i

and open_or_close_patterns' (ps:list (pattern & bool)) (v:open_or_close) (i:nat) 
  : GTot (list (pattern & bool))
         (decreases ps)
  = match ps with
    | [] -> ps
    | (p, b)::ps ->
      let n = binder_offset_pattern p in
      let p = open_or_close_pattern' p v i in
      let ps = open_or_close_patterns' ps v (i + n) in
      (p,b)::ps

and open_or_close_pattern' (p:pattern) (v:open_or_close) (i:nat) 
  : GTot pattern
         (decreases p)
  = match p with
    | Pat_Constant _ -> p

    | Pat_Cons fv us pats -> 
      let pats = open_or_close_patterns' pats v i in
      Pat_Cons fv us pats
      
    | Pat_Var bv ->
      Pat_Var (open_or_close_bv' bv v i)

    | Pat_Wild bv ->
      Pat_Wild (open_or_close_bv' bv v i)

    | Pat_Dot_Term topt ->
      Pat_Dot_Term (match topt with
                    | None -> None
                    | Some t -> Some (open_or_close_term' t v i))

    
and open_or_close_branch' (br:branch) (v:open_or_close) (i:nat)
  : GTot branch (decreases br)
  = let p, t = br in
    let p = open_or_close_pattern' p v i in
    let j = binder_offset_pattern p in
    let t = open_or_close_term' t v (i + j) in
    p, t
  
and open_or_close_branches' (brs:list branch) (v:open_or_close) (i:nat)
  : GTot (list branch) (decreases brs)
  = match brs with
    | [] -> []
    | br::brs -> open_or_close_branch' br v i :: open_or_close_branches' brs v i
  
and open_or_close_match_returns' (m:match_returns_ascription) (v:open_or_close) (i:nat)
  : GTot match_returns_ascription (decreases m)
  = let b, (ret, as_, eq) = m in
    let b = open_or_close_binder' b v i in
    let ret =
      match ret with
      | Inl t -> Inl (open_or_close_term' t v (i + 1))
      | Inr c -> Inr (open_or_close_comp' c v (i + 1))
    in
    let as_ =
      match as_ with
      | None -> None
      | Some t -> Some (open_or_close_term' t v (i + 1))
    in
    b, (ret, as_, eq)

let make_bv (n:int) (t:term) = { bv_ppname = "_"; bv_index = n; bv_sort = t}
let var_as_bv (v:int) = pack_bv (make_bv v (pack_ln Tv_Unknown))
let var_as_term (v:var) = pack_ln (Tv_Var (var_as_bv v))

assume
val open_with (t:term) (v:term)
  : term
  
assume
val open_with_spec (t v:term)
  : Lemma (open_with t v == open_or_close_term' t (OpenWith v) 0)

assume
val open_term (t:term) (v:var) 
  : term

assume
val open_term_spec (t:term) (v:var)
  : Lemma (open_term t v == open_or_close_term' t (OpenWithVar v) 0)
  
assume
val close_term (t:term) (v:var) 
  : term

assume
val close_term_spec (t:term) (v:var)
  : Lemma (close_term t v == open_or_close_term' t (CloseVar v) 0)

assume
val rename (t:term) (x y:var)
  : term

assume
val rename_spec (t:term) (x y:var)
  : Lemma (rename t x y == open_or_close_term' t (Rename x y) 0)
  
let bv_as_binder bv = pack_binder bv Q_Explicit []

let bv_index_of_make_bv (n:nat) (t:term)
  : Lemma (ensures bv_index (pack_bv (make_bv n t)) == n)
          [SMTPat (bv_index (pack_bv (make_bv n t)))]
  = ()

let constant_as_term (v:vconst) = pack_ln (Tv_Const v)
let unit_exp = constant_as_term C_Unit
let unit_fv = pack_fv unit_lid
let unit_ty = pack_ln (Tv_FVar unit_fv)
let bool_fv = pack_fv bool_lid
let bool_ty = pack_ln (Tv_FVar bool_fv)

let u_zero = pack_universe Uv_Zero
let u_max u1 u2 = pack_universe (Uv_Max [u1; u2])
let u_succ u = pack_universe (Uv_Succ u)
let mk_total t = pack_comp (C_Total t u_unk [])
let tm_type u = pack_ln (Tv_Type u)

let true_bool = pack_ln (Tv_Const C_True)
let false_bool = pack_ln (Tv_Const C_False)
let eq2 (t v0 v1:term) 
  : term 
  = let eq2 = pack_ln (Tv_FVar (pack_fv eq2_qn)) in
    let h = pack_ln (Tv_App eq2 (t, Q_Implicit)) in
    let h1 = pack_ln (Tv_App h (v0, Q_Explicit)) in
    let h2 = pack_ln (Tv_App h1 (v1, Q_Explicit)) in    
    h2

noeq
type constant_typing: vconst -> term -> Type0 = 
  | CT_Unit: constant_typing C_Unit unit_ty
  | CT_True: constant_typing C_True bool_ty
  | CT_False: constant_typing C_False bool_ty  

assume
val subtyping_token (e:env) (t0 t1:term) : Type0
assume
val check_subtyping (e:env) (t0 t1:term)
  : FStar.Tactics.Tac (option (subtyping_token e t0 t1))

assume
val equiv_token (e:env) (t0 t1:term) : Type0
assume
val check_equiv (e:env) (t0 t1:term)
  : FStar.Tactics.Tac (option (equiv_token e t0 t1))

noeq
type univ_eq : universe -> universe -> Type0 = 
  | UN_Refl : 
    u:universe ->
    univ_eq u u

  | UN_MaxCongL :
    u:universe ->
    u':universe ->
    v:universe ->
    univ_eq u u' ->
    univ_eq (u_max u v) (u_max u' v)

  | UN_MaxCongR :
    u:universe ->
    v:universe ->
    v':universe ->
    univ_eq v v' ->
    univ_eq (u_max u v) (u_max u v')

  | UN_MaxComm:
    u:universe ->
    v:universe ->
    univ_eq (u_max u v) (u_max v u)

  | UN_MaxLeq:
    u:universe ->
    v:universe ->
    univ_leq u v ->
    univ_eq (u_max u v) v

and univ_leq : universe -> universe -> Type0 = 
  | UNLEQ_Refl:
    u:universe ->
    univ_leq u u

  | UNLEQ_Succ:
    u:universe ->
    v:universe ->
    univ_leq u v ->
    univ_leq u (u_succ v)

  | UNLEQ_Max:
    u:universe ->
    v:universe ->
    univ_leq u (u_max u v)

noeq
type typing : env -> term -> term -> Type0 =
  | T_Var : 
     g:env ->
     x:bv { Some? (lookup_bvar g (bv_index x)) } ->
     typing g (pack_ln (Tv_Var x)) (Some?.v (lookup_bvar g (bv_index x)))

  | T_FVar :
     g:env ->
     x:fv { Some? (lookup_fvar g x) } -> 
     typing g (pack_ln (Tv_FVar x)) (Some?.v (lookup_fvar g x))

  | T_UInst :
     g:env ->
     x:fv ->
     us:list universe { Some? (lookup_fvar_uinst g x us) } ->
     typing g (pack_ln (Tv_UInst x us)) (Some?.v (lookup_fvar_uinst g x us))

  | T_Const:
     g:env ->
     v:vconst ->
     t:term ->
     constant_typing v t ->
     typing g (constant_as_term v) t

  | T_Abs :
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     ty:term ->
     body:term ->
     body_ty:term ->
     u:universe ->
     pp_name:string ->
     q:aqualv ->
     typing g ty (tm_type u) ->
     typing (extend_env g x ty) (open_term body x) body_ty ->
     typing g (pack_ln (Tv_Abs (mk_binder pp_name 0 ty q) body))
              (pack_ln (Tv_Arrow (mk_binder pp_name 0 ty q)
                                 (mk_total (close_term body_ty x))))

  | T_App :
     g:env ->
     e1:term ->
     e2:term ->
     x:binder ->
     t:term ->
     u:universe ->
     typing g e1 (pack_ln (Tv_Arrow x (pack_comp (C_Total t u [])))) ->
     typing g e2 (binder_sort x) ->
     typing g (pack_ln (Tv_App e1 (e2, binder_qual x)))
              (open_with t e2)

  | T_Arrow:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     t1:term ->
     t2:term ->
     u1:universe ->
     u2:universe ->
     pp_name:string ->
     q:aqualv ->
     typing g t1 (tm_type u1) ->
     typing (extend_env g x t1) (open_term t2 x) (tm_type u2) ->
     typing g (pack_ln (Tv_Arrow (mk_binder pp_name 0 t1 q) (mk_total t2)))
              (tm_type (u_max u1 u2))

  | T_Refine:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->     
     t:term ->
     e:term ->
     u1:universe ->
     u2:universe ->     
     typing g t (tm_type u1) ->
     typing (extend_env g x t) (open_term e x) (tm_type u2) ->
     typing g (pack_ln (Tv_Refine (pack_bv (make_bv 0 t)) e)) (tm_type u1)

  | T_Sub:
     g:env ->
     e:term ->
     t:term ->
     t':term ->
     typing g e t ->
     sub_typing g t t' ->
     typing g e t'

  | T_If: 
     g:env ->
     scrutinee:term ->
     then_:term ->
     else_:term ->
     ty:term ->
     hyp:var { None? (lookup_bvar g hyp) } ->
     typing g scrutinee bool_ty ->
     typing (extend_env g hyp (eq2 bool_ty scrutinee true_bool)) then_ ty ->
     typing (extend_env g hyp (eq2 bool_ty scrutinee false_bool)) else_ ty ->     
     typing g (pack_ln (Tv_Match scrutinee None [(Pat_Constant C_True, then_); 
                                                 (Pat_Constant C_False, else_)])) ty

  | T_Match: 
     g:env ->
     scrutinee:term ->
     i_ty:term ->
     branches:list branch ->
     ty:term ->
     typing g scrutinee i_ty ->
     branches_typing g scrutinee i_ty branches ty ->
     typing g (pack_ln (Tv_Match scrutinee None branches)) ty
    
and sub_typing : env -> term -> term -> Type0 =
  | ST_Equiv:
      g:env ->
      t0:term ->
      t1:term ->
      equiv g t0 t1 ->
      sub_typing g t0 t1

  | ST_Token: 
      g:env ->
      t0:term ->
      t1:term ->      
      subtyping_token g t0 t1 ->
      sub_typing g t0 t1

  | ST_UnivEq:
      g:env ->
      u:universe ->
      v:universe ->
      univ_eq u v ->
      sub_typing g (tm_type u) (tm_type v)

and equiv : env -> term -> term -> Type0 =
  | EQ_Refl:
      g:env ->
      t0:term ->
      equiv g t0 t0

  | EQ_Sym:
      g:env ->
      t0:term ->
      t1:term ->
      equiv g t0 t1 ->
      equiv g t1 t0

  | EQ_Trans:
      g:env ->
      t0:term ->
      t1:term ->
      t2:term ->
      equiv g t0 t1 ->
      equiv g t1 t2 ->
      equiv g t0 t2

  | EQ_Token:
      g:env ->
      t0:term ->
      t1:term ->
      equiv_token g t0 t1 ->
      equiv g t0 t1
      

and branches_typing : env -> term -> term -> list branch -> term -> Type0 =

let bindings = list (var & term)
let rename_bindings bs x y = FStar.List.Tot.map (fun (v, t) -> (v, rename t x y)) bs

let rec extend_env_l (g:env) (bs:bindings) 
  : env
  = match bs with
    | [] -> g
    | (x,t)::bs -> extend_env (extend_env_l g bs) x t

assume
val subtyping_token_renaming (g:env)
                             (bs0:bindings)
                             (bs1:bindings)
                             (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                             (y:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) y) })
                             (t:term)
                             (t0 t1:term)
                             (d:subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1)
  : subtyping_token (extend_env_l g (rename_bindings bs1 x y@(y,t)::bs0))
                    (rename t0 x y)
                    (rename t1 x y)

assume
val subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term)
                             (d:subtyping_token (extend_env_l g (bs1@bs0)) t0 t1)
  : subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1

let simplify_umax (#g:R.env) (#t:R.term) (#u:R.universe)
                  (d:typing g t (tm_type (u_max u u)))
   : typing g t (tm_type u)
   = let ue
       : univ_eq (u_max u u) u
       = UN_MaxLeq u u (UNLEQ_Refl u)
     in
     T_Sub _ _ _ _ d (ST_UnivEq _ _ _ ue)

#push-options "--query_stats --ifuel 2"

let rec ln' (e:term) (n:int)
  : bool
  = match inspect_ln e with
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown 
    | Tv_Var _ -> true
    | Tv_BVar m -> bv_index m <= n
    | Tv_App e1 (e2, _) -> ln' e1 n && ln' e2 n
    | Tv_Abs b body -> 
      ln'_binder b n &&
      ln' body (n + 1)

    | Tv_Arrow b c ->
      ln'_binder b n &&
      ln'_comp c (n + 1)

    | Tv_Refine bv f ->
      ln'_bv bv n &&
      ln' f (n + 1)

    | Tv_Uvar _ _ ->
      false
      
    | Tv_Let recf attrs bv def body ->
      ln'_terms attrs n &&
      ln'_bv bv n &&
      (if recf then ln' def (n + 1) else ln' def n) &&
      ln' body (n + 1)

    | Tv_Match scr ret brs ->
      ln' scr n &&
      (match ret with
      | None -> true
      | Some m -> ln'_match_returns m n) &&
      ln'_branches brs n
      
    | Tv_AscribedT e t tac b ->
      ln' e n &&
      ln' t n &&
      (match tac with
       | None -> true
       | Some tac -> ln' tac n)
                            
    | Tv_AscribedC e c tac b ->
      ln' e n &&
      ln'_comp c n &&
      (match tac with
       | None -> true
       | Some tac -> ln' tac n)
                            
    | _ -> false

and ln'_comp (c:comp) (i:int)
  : Tot bool (decreases c)
  = match inspect_comp c with
    | C_Total t u decr
    | C_GTotal t u decr ->
      ln' t i &&
      ln'_terms decr i

    | C_Lemma pre post pats ->
      ln' pre i &&
      ln' post i &&
      ln' pats i

    | C_Eff us eff_name res args ->
      ln' res i &&
      ln'_args args i

and ln'_args (ts:list argv) (i:int)
  : Tot bool (decreases ts)
  = match ts with
    | [] -> true
    | (t,q)::ts -> 
      ln' t i &&
      ln'_args ts i

and ln'_bv (b:bv) (n:int) 
  : Tot bool (decreases b)
  = let bv = inspect_bv b in
    ln' bv.bv_sort n
    
and ln'_binder (b:binder) (n:int)
  : Tot bool (decreases b)
  = let bndr  = inspect_binder b in
    let bv, (q, attrs) = bndr in
    ln'_bv bv n &&
    ln'_terms attrs n

and ln'_terms (ts:list term) (n:int)
  : Tot bool (decreases ts)
  = match ts with
    | [] -> true
    | t::ts -> ln' t n && ln'_terms ts n

and ln'_patterns (ps:list (pattern & bool)) (i:int)
  : Tot bool
    (decreases ps)
  = match ps with
    | [] -> true
    | (p, b)::ps ->
      let b0 = ln'_pattern p i in
      let n = binder_offset_pattern p in
      let b1 = ln'_patterns ps (i + n) in
      b0 && b1

and ln'_pattern (p:pattern) (i:int) 
  : Tot bool
        (decreases p)
  = match p with
    | Pat_Constant _ -> true

    | Pat_Cons fv us pats -> 
      ln'_patterns pats i
      
    | Pat_Var bv 
    | Pat_Wild bv ->
      ln'_bv bv i

    | Pat_Dot_Term topt ->
      (match topt with
       | None -> true
       | Some t -> ln' t i)
    
and ln'_branch (br:branch) (i:int)
  : Tot bool (decreases br)
  = let p, t = br in
    let b = ln'_pattern p i in
    let j = binder_offset_pattern p in
    let b' = ln' t (i + j) in
    b&&b'
  
and ln'_branches (brs:list branch) (i:int)
  : Tot bool (decreases brs)
  = match brs with
    | [] -> true
    | br::brs -> 
      ln'_branch br i &&
      ln'_branches brs i
  
and ln'_match_returns (m:match_returns_ascription) (i:int)
  : Tot bool (decreases m)
  = let b, (ret, as_, eq) = m in
    let b = ln'_binder b i in
    let ret =
      match ret with
      | Inl t -> ln' t (i + 1)
      | Inr c -> ln'_comp c (i + 1)
    in
    let as_ =
      match as_ with
      | None -> true
      | Some t -> ln' t (i + 1)
    in
    b && ret && as_

let ln (t:term) = ln' t (-1)
let ln_comp (c:comp) = ln'_comp c (-1)

assume
val well_typed_terms_are_ln (g:R.env) (e:R.term) (t:R.term) (_:typing g e t)
  : Lemma (ensures ln e)

assume
val type_correctness (g:R.env) (e:R.term) (t:R.term) (_:typing g e t)
  : GTot (u:R.universe & typing g t (tm_type u))

let rec binder_offset_pattern_invariant (p:pattern) (s:open_or_close) (i:nat)
  : Lemma (binder_offset_pattern p == binder_offset_pattern (open_or_close_pattern' p s i))
  = match p with
    | Pat_Cons _ _ pats ->
      binder_offset_patterns_invariant pats s i
    | _ -> ()

and binder_offset_patterns_invariant (p:list (pattern & bool)) (s:open_or_close) (i:nat)
  : Lemma (binder_offset_patterns p == binder_offset_patterns (open_or_close_patterns' p s i))
  = match p with
    | [] -> ()
    | (hd, _)::tl ->
      binder_offset_pattern_invariant hd s i;
      let n = binder_offset_pattern hd in
      binder_offset_patterns_invariant tl s (i + n)
  

let rec open_close_inverse (i:nat) (t:term { ln' t (i - 1) }) (x:var)
  : Lemma 
       (ensures open_or_close_term' 
                       (open_or_close_term' t (CloseVar x) i)
                       (OpenWithVar x)
                       i
                == t)
       (decreases t)
  = match inspect_ln t with
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown -> ()
    | Tv_Var _ -> ()
    | Tv_BVar _ -> ()
    | Tv_App t1 a ->
      open_close_inverse i t1 x;
      open_close_inverse i (fst a) x
     
    | Tv_Abs b body -> 
      open_close_inverse_binder i b x;
      open_close_inverse (i + 1) body x

    | Tv_Arrow b c ->
      open_close_inverse_binder i b x;
      open_close_inverse_comp (i + 1) c x

    | Tv_Refine b f ->
      open_close_inverse_bv i b x;
      open_close_inverse (i + 1) f x
      
    | Tv_Let recf attrs bv def body ->
      open_close_inverse_terms i attrs x;
      open_close_inverse_bv i bv x;
      (if recf 
      then open_close_inverse (i + 1) def x
      else open_close_inverse i def x);
      open_close_inverse (i + 1) body x

    | Tv_Match scr ret brs ->
      open_close_inverse i scr x;
      (match ret with
       | None -> ()
       | Some m -> open_close_inverse_match_returns i m x);
      open_close_inverse_branches i brs x
      
    | Tv_AscribedT e t tac b ->
      open_close_inverse i e x;
      open_close_inverse i t x;      
      (match tac with
       | None -> ()
       | Some tac -> open_close_inverse i tac x)

    | Tv_AscribedC e c tac b ->
      open_close_inverse i e x;
      open_close_inverse_comp i c x;      
      (match tac with
       | None -> ()
       | Some tac -> open_close_inverse i tac x)
    

and open_close_inverse_bv (i:nat) (b:bv { ln'_bv b (i - 1) }) (x:var) 
  : Lemma (ensures open_or_close_bv' (open_or_close_bv' b (CloseVar x) i)
                                     (OpenWithVar x)
                                     i
                   == b)
          (decreases b)
  = let bv = inspect_bv b in
    open_close_inverse i bv.bv_sort x
    
and open_close_inverse_binder (i:nat) (b:binder { ln'_binder b (i - 1) }) (x:var)
  : Lemma (ensures open_or_close_binder'
                         (open_or_close_binder' b (CloseVar x) i)
                         (OpenWithVar x)
                         i
                   == b)
          (decreases b)                   
  = let bndr  = inspect_binder b in
    assert (bndr << b);
    let bv, (q, attrs) = bndr in
    open_close_inverse_bv i bv x;
    open_close_inverse_terms i attrs x;
    assert (open_or_close_bv' (open_or_close_bv' bv (CloseVar x) i) (OpenWithVar x) i == bv);
    assert (open_or_close_terms' (open_or_close_terms' attrs (CloseVar x) i) (OpenWithVar x) i == attrs);    
    pack_inspect_binder b;    
    assert (pack_binder bv q attrs == b)

and open_close_inverse_terms (i:nat) (ts:list term { ln'_terms ts (i - 1) }) (x:var)
  : Lemma (ensures open_or_close_terms' (open_or_close_terms' ts (CloseVar x) i)
                                        (OpenWithVar x)
                                        i
                   == ts)
          (decreases ts)                   
  = match ts with
    | [] -> ()
    | t::ts -> 
      open_close_inverse i t x;
      open_close_inverse_terms i ts x

and open_close_inverse_comp (i:nat) (c:comp { ln'_comp c (i - 1) }) (x:var)
  : Lemma 
    (ensures open_or_close_comp' (open_or_close_comp' c (CloseVar x) i)
                              (OpenWithVar x)
                              i
             == c)
    (decreases c)
  = match inspect_comp c with
    | C_Total t u decr
    | C_GTotal t u decr ->    
      open_close_inverse i t x;
      open_close_inverse_terms i decr x


    | C_Lemma pre post pats ->
      open_close_inverse i pre x;
      open_close_inverse i post x;
      open_close_inverse i pats x

    | C_Eff us eff_name res args ->
      open_close_inverse i res x;
      open_close_inverse_args i args x
      

and open_close_inverse_args (i:nat) 
                            (ts:list argv { ln'_args ts (i - 1) })
                            (x:var)
  : Lemma
    (ensures open_or_close_args' (open_or_close_args' ts (CloseVar x) i)
                                 (OpenWithVar x)
                                 i
             == ts)
    (decreases ts)
  = match ts with
    | [] -> ()
    | (t,q)::ts -> 
      open_close_inverse i t x;
      open_close_inverse_args i ts x

and open_close_inverse_patterns (i:nat)
                                (ps:list (pattern & bool) { ln'_patterns ps (i - 1) })
                                (x:var)
  : Lemma 
    (ensures open_or_close_patterns' (open_or_close_patterns' ps (CloseVar x) i)
                                     (OpenWithVar x)
                                     i
             == ps)
    (decreases ps)
  = match ps with
    | [] -> ()
    | (p, b)::ps' ->
      open_close_inverse_pattern i p x;
      let n = binder_offset_pattern p in
      binder_offset_pattern_invariant p (CloseVar x) i;
      open_close_inverse_patterns (i + n) ps' x

and open_close_inverse_pattern (i:nat) (p:pattern{ln'_pattern p (i - 1)}) (x:var)
  : Lemma 
    (ensures open_or_close_pattern' (open_or_close_pattern' p (CloseVar x) i)
                                    (OpenWithVar x)
                                      i
             == p)
    (decreases p)
  = match p with
    | Pat_Constant _ -> ()

    | Pat_Cons fv us pats -> 
      open_close_inverse_patterns i pats x
      
    | Pat_Var bv
    | Pat_Wild bv ->
      open_close_inverse_bv i bv x

    | Pat_Dot_Term topt ->
      match topt with
      | None -> ()
      | Some t -> open_close_inverse i t x

    
and open_close_inverse_branch (i:nat) (br:branch{ln'_branch br (i - 1)}) (x:var)
  : Lemma
    (ensures open_or_close_branch'
                 (open_or_close_branch' br (CloseVar x) i)
                 (OpenWithVar x)
                 i
             == br)
    (decreases br)  
  = let p, t = br in
    let j = binder_offset_pattern p in
    binder_offset_pattern_invariant p (CloseVar x) i;
    open_close_inverse_pattern i p x;
    open_close_inverse (i + j) t x
  
and open_close_inverse_branches (i:nat)
                                (brs:list branch { ln'_branches brs (i - 1) })
                                (x:var)
  : Lemma
    (ensures open_or_close_branches'
                 (open_or_close_branches' brs (CloseVar x) i)
                 (OpenWithVar x)
                 i
             == brs)
    (decreases brs)
  = match brs with
    | [] -> ()
    | br::brs -> 
      open_close_inverse_branch i br x;
      open_close_inverse_branches i brs x
  
and open_close_inverse_match_returns (i:nat) 
                                     (m:match_returns_ascription { ln'_match_returns m (i - 1) })
                                     (x:var)
  : Lemma 
    (ensures open_or_close_match_returns' 
                 (open_or_close_match_returns' m (CloseVar x) i)
                 (OpenWithVar x)
                 i
             == m)
    (decreases m)
  = let b, (ret, as_, eq) = m in
    open_close_inverse_binder i b x;
    let ret =
      match ret with
      | Inl t ->
        open_close_inverse (i + 1) t x
      | Inr c ->
        open_close_inverse_comp (i + 1) c x
    in
    let as_ =
      match as_ with
      | None -> ()
      | Some t ->
        open_close_inverse (i + 1) t x
    in
    ()

