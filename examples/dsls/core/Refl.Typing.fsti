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
  
val inspect_pack_binder (b:_) (q:_) (a:_)
  : Lemma (ensures R.(R.inspect_binder (R.pack_binder b q a) == (b, (q, a))))
          [SMTPat R.(inspect_binder (pack_binder b q a))]

val pack_inspect_binder (t:R.binder)
  : Lemma (ensures (let b, (q, a) = R.inspect_binder t in
                    R.(pack_binder b q a == t)))

let pack_inspect_comp (t:R.comp)
  : Lemma (ensures (R.pack_comp (R.inspect_comp t) == t))
          [SMTPat (R.pack_comp (R.inspect_comp t))]
  = R.pack_inspect_comp_inv t
  
let inspect_pack_comp (t:R.comp_view)
  : Lemma (ensures (R.inspect_comp (R.pack_comp t) == t))
          [SMTPat (R.inspect_comp (R.pack_comp t))]
  = R.inspect_pack_comp_inv t
  
val lookup_bvar (e:env) (x:int) : option term

val lookup_fvar (e:env) (x:fv) : option term

val extend_env (e:env) (x:var) (ty:term) : env

val lookup_bvar_extend_env (g:env) (x y:var) (ty:term)
  : Lemma 
    (ensures (
           if x = y
           then lookup_bvar (extend_env g x ty) y == Some ty
           else lookup_bvar (extend_env g x ty) y == lookup_bvar g y))
    [SMTPat (lookup_bvar (extend_env g x ty) y)]

val lookup_fvar_extend_env (g:env) (x:fv) (y:var) (ty:term)
  : Lemma 
    (ensures lookup_fvar (extend_env g y ty) x == lookup_fvar g x)
    [SMTPat (lookup_fvar (extend_env g y ty) x)]

let as_binder (x:var) (ty:term)
  : binder 
  = pack_binder
      (pack_bv ({bv_ppname="";
                 bv_index=x;
                 bv_sort=ty}))
      Q_Explicit
      []

let bv_index (x:bv) : int = (inspect_bv x).bv_index


let binder_sort (b:binder) =
  let bv, _ = inspect_binder b in 
  (inspect_bv bv).bv_sort

let binder_sort_lemma (x:var) (ty:term)
  : Lemma (binder_sort (as_binder x ty) == ty)
          [SMTPat (binder_sort (as_binder x ty))]
  = ()          

//replace BV 0 in t with v
noeq
type open_or_close =
  | OpenWith of term
  | CloseVar of var
  | Rename   : var -> var -> open_or_close

val open_or_close_ctx_uvar_and_subst (c:ctx_uvar_and_subst) (v:open_or_close) (i:nat) 
  : ctx_uvar_and_subst
  
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
       | OpenWith _ -> t
       | CloseVar y ->
         if bv_index x = y 
         then pack_ln (Tv_BVar (pack_bv ({ inspect_bv x with bv_index = i })))
         else t
       | Rename y z ->
         if bv_index x = y
         then pack_ln (Tv_Var (pack_bv ({ inspect_bv x with bv_index = z })))
         else t)

    | Tv_BVar j -> 
      (match v with
       | Rename _ _ -> t
       | CloseVar _ -> t
       | OpenWith v ->
         if i=bv_index j 
          then v
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
    assume (bndr << b);
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
  : GTot (list (pattern & bool) & nat)
         (decreases ps)
  = match ps with
    | [] -> ps, 0
    | (p, b)::ps ->
      let (p, n) = open_or_close_pattern' p v i in
      let (ps, m) = open_or_close_patterns' ps v (i + n) in
      (p,b)::ps, n + m

and open_or_close_pattern' (p:pattern) (v:open_or_close) (i:nat) 
  : GTot (pattern & nat)
         (decreases p)
  = match p with
    | Pat_Constant _ -> p,0

    | Pat_Cons fv us pats -> 
      let pats, n = open_or_close_patterns' pats v i in
      Pat_Cons fv us pats, n
      
    | Pat_Var bv ->
      Pat_Var (open_or_close_bv' bv v i), 1

    | Pat_Wild bv ->
      Pat_Wild (open_or_close_bv' bv v i), 1

    | Pat_Dot_Term topt ->
      Pat_Dot_Term (match topt with
                    | None -> None
                    | Some t -> Some (open_or_close_term' t v i)), 0

    
and open_or_close_branch' (br:branch) (v:open_or_close) (i:nat)
  : GTot branch (decreases br)
  = let p, t = br in
    let p, j = open_or_close_pattern' p v i in
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

let make_bv (n:nat) (t:term) = { bv_ppname = "_"; bv_index = n; bv_sort = t}
let var_as_bv (v:var) = pack_bv (make_bv v (pack_ln Tv_Unknown))
let var_as_term (v:var) = pack_ln (Tv_Var (var_as_bv v))

val open_with (t:term) (v:term)
  : term
  
val open_with_spec (t v:term)
  : Lemma (open_with t v == open_or_close_term' t (OpenWith v) 0)

val open_term (t:term) (v:var) 
  : term

val open_term_spec (t:term) (v:var)
  : Lemma (open_term t v == open_or_close_term' t (OpenWith (var_as_term v)) 0)
  
val close_term (t:term) (v:var) 
  : term

val close_term_spec (t:term) (v:var)
  : Lemma (close_term t v == open_or_close_term' t (CloseVar v) 0)

val rename (t:term) (x y:var)
  : term

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

val subtyping_token (e:env) (t0 t1:term) : Type0
val check_subtyping (e:env) (t0 t1:term)
  : FStar.Tactics.Tac (option (subtyping_token e t0 t1))

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
     typing g ty (tm_type u) ->
     typing (extend_env g x ty) (open_term body x) body_ty ->
     typing g (pack_ln (Tv_Abs (as_binder 0 ty) body))
              (pack_ln (Tv_Arrow (as_binder 0 ty) 
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
     typing g (pack_ln (Tv_App e1 (e2, Q_Explicit)))
              (open_with t e2)

  | T_Arrow:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     t1:term ->
     t2:term ->
     u1:universe ->
     u2:universe ->
     typing g t1 (tm_type u1) ->
     typing (extend_env g x t1) (open_term t2 x) (tm_type u2) ->
     typing g (pack_ln (Tv_Arrow (as_binder 0 t1) (mk_total t2)))
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
  | ST_Refl: 
      g:env ->
      t:term ->
      sub_typing g t t

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

and branches_typing : env -> term -> term -> list branch -> term -> Type0 =

let bindings = list (var & term)
let rename_bindings bs x y = FStar.List.Tot.map (fun (v, t) -> (v, rename t x y)) bs

let rec extend_env_l (g:env) (bs:bindings) 
  : env
  = match bs with
    | [] -> g
    | (x,t)::bs -> extend_env (extend_env_l g bs) x t

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


