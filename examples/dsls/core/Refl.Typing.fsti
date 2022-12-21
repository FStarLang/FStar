module Refl.Typing

open FStar.List.Tot
open FStar.Reflection
module R = FStar.Reflection
module T = FStar.Tactics
module FTB = FStar.Tactics.Builtins

val inspect_pack (t:R.term_view)
  : Lemma (ensures R.(inspect_ln (pack_ln t) == t))
          [SMTPat R.(inspect_ln (pack_ln t))]
  
val pack_inspect (t:R.term)
  : Lemma (ensures R.(pack_ln (inspect_ln t) == t))
          [SMTPat R.(pack_ln (inspect_ln t))]
  
val inspect_pack_bv (t:R.bv_view)
  : Lemma (ensures R.(inspect_bv (pack_bv t) == t))
          [SMTPat R.(inspect_bv (pack_bv t))]
  
val pack_inspect_bv (t:R.bv)
  : Lemma (ensures R.(pack_bv (inspect_bv t) == t))
          [SMTPat R.(pack_bv (inspect_bv t))]
  
val inspect_pack_binder (b:_) (q:_) (a:_)
  : Lemma (ensures R.(R.inspect_binder (R.pack_binder b q a) == (b, (q, a))))
          [SMTPat R.(inspect_binder (pack_binder b q a))]
  
val pack_inspect_binder (t:R.binder)
  : Lemma (ensures (let b, (q, a) = R.inspect_binder t in
                    R.(pack_binder b q a == t)))
  
val pack_inspect_comp (t:R.comp)
  : Lemma (ensures (R.pack_comp (R.inspect_comp t) == t))
          [SMTPat (R.pack_comp (R.inspect_comp t))]
  
val inspect_pack_comp (t:R.comp_view)
  : Lemma (ensures (R.inspect_comp (R.pack_comp t) == t))
          [SMTPat (R.inspect_comp (R.pack_comp t))]

val pack_inspect_fv (fv:R.fv)
  : Lemma (ensures R.pack_fv (R.inspect_fv fv) == fv)
          [SMTPat (R.pack_fv (R.inspect_fv fv))]

val inspect_pack_fv (nm:R.name)
  : Lemma (ensures R.inspect_fv (R.pack_fv nm) == nm)
          [SMTPat (R.inspect_fv (R.pack_fv nm))]

val pack_inspect_universe (u:R.universe)
  : Lemma (ensures R.pack_universe (R.inspect_universe u) == u)
          [SMTPat (R.pack_universe (R.inspect_universe u))]

val inspect_pack_universe (u:R.universe_view)
  : Lemma (ensures R.inspect_universe (R.pack_universe u) == u)
          [SMTPat (R.inspect_universe (R.pack_universe u))]

val lookup_bvar (e:env) (x:int) : option term

val lookup_fvar_uinst (e:R.env) (x:R.fv) (us:list R.universe) : option R.term

let lookup_fvar (e:env) (x:fv) : option term = lookup_fvar_uinst e x []

let mk_binder (pp_name:string) (x:var) (ty:term) (q:aqualv)
  = pack_binder
      (pack_bv ({bv_ppname=pp_name;
                 bv_index=x;
                 bv_sort=ty}))
      q
      []

let extend_env (e:env) (x:var) (ty:term) : env =
  R.push_binder e (mk_binder "x" x ty Q_Explicit)
  
val lookup_bvar_extend_env (g:env) (x y:var) (ty:term)
  : Lemma 
    (ensures (
           if x = y
           then lookup_bvar (extend_env g x ty) y == Some ty
           else lookup_bvar (extend_env g x ty) y == lookup_bvar g y))
    [SMTPat (lookup_bvar (extend_env g x ty) y)]

val lookup_fvar_extend_env (g:env) (x:fv) (us:universes) (y:var) (ty:term)
  : Lemma 
    (ensures lookup_fvar_uinst (extend_env g y ty) x us == lookup_fvar_uinst g x us)
    [SMTPat (lookup_fvar_uinst (extend_env g y ty) x us)]

let as_binder (x:var) (ty:term) =
  mk_binder "x" x ty Q_Explicit

let bv_index (x:bv)
  : var
  = let n = (inspect_bv x).bv_index in
    assume (n >= 0); //TODO: fix lib
    n

let binder_sort (b:binder) =
  let bv, _ = inspect_binder b in 
  (inspect_bv bv).bv_sort

let binder_qual (b:binder) =
  let _, (q, _) = inspect_binder b in q

noeq
type open_or_close =
  | OpenWith of term
  | CloseVar of var
  | Rename   : var -> var -> open_or_close

let tun = pack_ln Tv_Unknown

let make_bv (n:int) (t:term) = { bv_ppname = "_"; bv_index = n; bv_sort = t}
let make_bv_with_name (s:string) (n:int) (t:term) =
  { bv_ppname = s; bv_index = n; bv_sort = t}
let var_as_bv (v:int) = pack_bv (make_bv v tun)
let var_as_term (v:var) = pack_ln (Tv_Var (var_as_bv v))
            
let open_with_var (x:var) = OpenWith (pack_ln (Tv_Var (var_as_bv x)))
  
let maybe_index_of_term (x:term) =
  match inspect_ln x with
  | Tv_Var bv -> Some (bv_index bv)
  | _ -> None
  
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
  : Tot term (decreases t)
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
         then (
           match maybe_index_of_term v with
           | None -> v
           | Some k ->
             //if we're substituting a name j for a name k, retain the pp_name of j
             pack_ln (Tv_Var (pack_bv { inspect_bv j with bv_index = k }))
         )
         else t
      )

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
  : Tot bv (decreases b)
  = let bv = inspect_bv b in
    pack_bv ({bv with bv_sort = open_or_close_term' bv.bv_sort v i})

and open_or_close_binder' (b:binder) (v:open_or_close) (i:nat)
  : Tot binder (decreases b)
  = let bndr  = inspect_binder b in
    let bv, (q, attrs) = bndr in
    pack_binder (open_or_close_bv' bv v i) 
                q
                (open_or_close_terms' attrs v i)

and open_or_close_comp' (c:comp) (v:open_or_close) (i:nat)
  : Tot comp (decreases c)
  = match inspect_comp c with
    | C_Total t ->
      pack_comp (C_Total (open_or_close_term' t v i))

    | C_GTotal t ->
      pack_comp (C_GTotal (open_or_close_term' t v i))

    | C_Lemma pre post pats ->
      pack_comp (C_Lemma (open_or_close_term' pre v i)
                         (open_or_close_term' post v i)
                         (open_or_close_term' pats v i))

    | C_Eff us eff_name res args decrs ->
      pack_comp (C_Eff us eff_name
                       (open_or_close_term' res v i)
                       (open_or_close_args' args v i)
                       (open_or_close_terms' decrs v i))

and open_or_close_terms' (ts:list term) (v:open_or_close) (i:nat)
  : Tot (list term) (decreases ts)
  = match ts with
    | [] -> []
    | t::ts -> open_or_close_term' t v i :: open_or_close_terms' ts v i

and open_or_close_args' (ts:list argv) (v:open_or_close) (i:nat)
  : Tot (list argv) (decreases ts)
  = match ts with
    | [] -> []
    | (t,q)::ts -> (open_or_close_term' t v i,q) :: open_or_close_args' ts v i

and open_or_close_patterns' (ps:list (pattern & bool)) (v:open_or_close) (i:nat) 
  : Tot (list (pattern & bool))
         (decreases ps)
  = match ps with
    | [] -> ps
    | (p, b)::ps ->
      let n = binder_offset_pattern p in
      let p = open_or_close_pattern' p v i in
      let ps = open_or_close_patterns' ps v (i + n) in
      (p,b)::ps

and open_or_close_pattern' (p:pattern) (v:open_or_close) (i:nat) 
  : Tot pattern
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
  : Tot branch (decreases br)
  = let p, t = br in
    let p = open_or_close_pattern' p v i in
    let j = binder_offset_pattern p in
    let t = open_or_close_term' t v (i + j) in
    p, t
  
and open_or_close_branches' (brs:list branch) (v:open_or_close) (i:nat)
  : Tot (list branch) (decreases brs)
  = match brs with
    | [] -> []
    | br::brs -> open_or_close_branch' br v i :: open_or_close_branches' brs v i
  
and open_or_close_match_returns' (m:match_returns_ascription) (v:open_or_close) (i:nat)
  : Tot match_returns_ascription (decreases m)
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


val open_with (t:term) (v:term) : term
  
val open_with_spec (t v:term)
  : Lemma (open_with t v == open_or_close_term' t (OpenWith v) 0)

val open_term (t:term) (v:var) : term

val open_term_spec (t:term) (v:var)
  : Lemma (open_term t v == open_or_close_term' t (open_with_var v) 0)
  
val close_term (t:term) (v:var) : term

val close_term_spec (t:term) (v:var)
  : Lemma (close_term t v == open_or_close_term' t (CloseVar v) 0)

val rename (t:term) (x y:var) : term

val rename_spec (t:term) (x y:var)
  : Lemma (rename t x y == open_or_close_term' t (Rename x y) 0)
  
let bv_as_binder bv = pack_binder bv Q_Explicit []

val bv_index_of_make_bv (n:nat) (t:term)
  : Lemma (ensures bv_index (pack_bv (make_bv n t)) == n)
          [SMTPat (bv_index (pack_bv (make_bv n t)))]

let constant_as_term (v:vconst) = pack_ln (Tv_Const v)
let unit_exp = constant_as_term C_Unit
let unit_fv = pack_fv unit_lid
let unit_ty = pack_ln (Tv_FVar unit_fv)
let bool_fv = pack_fv bool_lid
let bool_ty = pack_ln (Tv_FVar bool_fv)

let u_zero = pack_universe Uv_Zero
let u_max u1 u2 = pack_universe (Uv_Max [u1; u2])
let u_succ u = pack_universe (Uv_Succ u)
let mk_total t = pack_comp (C_Total t)
let tm_type u = pack_ln (Tv_Type u)
let tm_prop = 
  let prop_fv = R.pack_fv ["Prims"; "prop"] in
  R.pack_ln (Tv_FVar prop_fv)
let eqtype_lid : R.name = ["Prims"; "eqtype"]

let true_bool = pack_ln (Tv_Const C_True)
let false_bool = pack_ln (Tv_Const C_False)
let eq2 (t v0 v1:term) 
  : term 
  = let eq2 = pack_ln (Tv_FVar (pack_fv eq2_qn)) in
    let h = pack_ln (Tv_App eq2 (t, Q_Implicit)) in
    let h1 = pack_ln (Tv_App h (v0, Q_Explicit)) in
    let h2 = pack_ln (Tv_App h1 (v1, Q_Explicit)) in    
    h2

let b2t_lid : R.name = ["Prims"; "b2t"]
let b2t_fv : R.fv = R.pack_fv b2t_lid
let b2t_ty : R.term = R.(pack_ln (Tv_Arrow (as_binder 0 bool_ty) (mk_total (tm_type u_zero))))



noeq
type constant_typing: vconst -> term -> Type0 = 
  | CT_Unit: constant_typing C_Unit unit_ty
  | CT_True: constant_typing C_True bool_ty
  | CT_False: constant_typing C_False bool_ty

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
  | T_Token :
    g:env ->
    e:term ->
    t:typ ->
    squash (FTB.typing_token g e t) ->
    typing g e t

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
     typing g e1 (pack_ln (Tv_Arrow x (pack_comp (C_Total t)))) ->
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

  | T_PropIrrelevance:
     g:env -> 
     e:term -> 
     t:term ->
     typing g e t ->
     typing g t tm_prop ->
     typing g (`()) t
     
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
      squash (FTB.subtyping_token g t0 t1) ->
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
      squash (FTB.equiv_token g t0 t1) ->
      equiv g t0 t1
      

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
                             (d:FTB.subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1)
  : FTB.subtyping_token (extend_env_l g (rename_bindings bs1 x y@(y,t)::bs0))
                        (rename t0 x y)
                        (rename t1 x y)

val subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term)
                              (d:FTB.subtyping_token (extend_env_l g (bs1@bs0)) t0 t1)
  : FTB.subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1

let simplify_umax (#g:R.env) (#t:R.term) (#u:R.universe)
                  (d:typing g t (tm_type (u_max u u)))
   : typing g t (tm_type u)
   = let ue
       : univ_eq (u_max u u) u
       = UN_MaxLeq u u (UNLEQ_Refl u)
     in
     T_Sub _ _ _ _ d (ST_UnivEq _ _ _ ue)

#push-options "--ifuel 2"

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
                            
and ln'_comp (c:comp) (i:int)
  : Tot bool (decreases c)
  = match inspect_comp c with
    | C_Total t
    | C_GTotal t -> ln' t i

    | C_Lemma pre post pats ->
      ln' pre i &&
      ln' post i &&
      ln' pats i

    | C_Eff us eff_name res args decrs ->
      ln' res i &&
      ln'_args args i &&
      ln'_terms decrs i

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

val well_typed_terms_are_ln (g:R.env) (e:R.term) (t:R.term) (_:typing g e t)
  : Lemma (ensures ln e)

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

let rec open_close_inverse' (i:nat) (t:term { ln' t (i - 1) }) (x:var)
  : Lemma 
       (ensures open_or_close_term' 
                       (open_or_close_term' t (CloseVar x) i)
                       (open_with_var x)
                       i
                == t)
       (decreases t)
  = match inspect_ln t with
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown
    | Tv_Var _ 
    | Tv_BVar _ -> ()
    | Tv_App t1 a ->
      open_close_inverse' i t1 x;
      open_close_inverse' i (fst a) x
     
     | Tv_Abs b body -> 
      open_close_inverse'_binder i b x;
      open_close_inverse' (i + 1) body x

    | Tv_Arrow b c ->
      open_close_inverse'_binder i b x;
      open_close_inverse'_comp (i + 1) c x

    | Tv_Refine b f ->
      open_close_inverse'_bv i b x;
      open_close_inverse' (i + 1) f x
      
    | Tv_Let recf attrs bv def body ->
      open_close_inverse'_terms i attrs x;
      open_close_inverse'_bv i bv x;
      (if recf 
      then open_close_inverse' (i + 1) def x
      else open_close_inverse' i def x);
      open_close_inverse' (i + 1) body x

    | Tv_Match scr ret brs ->
      open_close_inverse' i scr x;
      (match ret with
       | None -> ()
       | Some m -> open_close_inverse'_match_returns i m x);
      open_close_inverse'_branches i brs x
      
    | Tv_AscribedT e t tac b ->
      open_close_inverse' i e x;
      open_close_inverse' i t x;      
      (match tac with
       | None -> ()
       | Some tac -> open_close_inverse' i tac x)

    | Tv_AscribedC e c tac b ->
      open_close_inverse' i e x;
      open_close_inverse'_comp i c x;      
      (match tac with
       | None -> ()
       | Some tac -> open_close_inverse' i tac x)
    

and open_close_inverse'_bv (i:nat) (b:bv { ln'_bv b (i - 1) }) (x:var) 
  : Lemma (ensures open_or_close_bv' (open_or_close_bv' b (CloseVar x) i)
                                     (open_with_var x)
                                     i
                   == b)
          (decreases b)
  = let bv = inspect_bv b in
    open_close_inverse' i bv.bv_sort x
    
and open_close_inverse'_binder (i:nat) (b:binder { ln'_binder b (i - 1) }) (x:var)
  : Lemma (ensures open_or_close_binder'
                         (open_or_close_binder' b (CloseVar x) i)
                         (open_with_var x)
                         i
                   == b)
          (decreases b)                   
  = let bndr  = inspect_binder b in
    assert (bndr << b);
    let bv, (q, attrs) = bndr in
    open_close_inverse'_bv i bv x;
    open_close_inverse'_terms i attrs x;
    assert (open_or_close_bv' (open_or_close_bv' bv (CloseVar x) i) (open_with_var x) i == bv);
    assert (open_or_close_terms' (open_or_close_terms' attrs (CloseVar x) i) (open_with_var x) i == attrs);    
    pack_inspect_binder b;    
    assert (pack_binder bv q attrs == b)

and open_close_inverse'_terms (i:nat) (ts:list term { ln'_terms ts (i - 1) }) (x:var)
  : Lemma (ensures open_or_close_terms' (open_or_close_terms' ts (CloseVar x) i)
                                        (open_with_var x)
                                        i
                   == ts)
          (decreases ts)                   
  = match ts with
    | [] -> ()
    | t::ts -> 
      open_close_inverse' i t x;
      open_close_inverse'_terms i ts x

and open_close_inverse'_comp (i:nat) (c:comp { ln'_comp c (i - 1) }) (x:var)
  : Lemma 
    (ensures open_or_close_comp' (open_or_close_comp' c (CloseVar x) i)
                              (open_with_var x)
                              i
             == c)
    (decreases c)
  = match inspect_comp c with
    | C_Total t
    | C_GTotal t -> open_close_inverse' i t x

    | C_Lemma pre post pats ->
      open_close_inverse' i pre x;
      open_close_inverse' i post x;
      open_close_inverse' i pats x

    | C_Eff us eff_name res args decrs ->
      open_close_inverse' i res x;
      open_close_inverse'_args i args x;
      open_close_inverse'_terms i decrs x          

and open_close_inverse'_args (i:nat) 
                            (ts:list argv { ln'_args ts (i - 1) })
                            (x:var)
  : Lemma
    (ensures open_or_close_args' (open_or_close_args' ts (CloseVar x) i)
                                 (open_with_var x)
                                 i
             == ts)
    (decreases ts)
  = match ts with
    | [] -> ()
    | (t,q)::ts -> 
      open_close_inverse' i t x;
      open_close_inverse'_args i ts x

and open_close_inverse'_patterns (i:nat)
                                (ps:list (pattern & bool) { ln'_patterns ps (i - 1) })
                                (x:var)
  : Lemma 
    (ensures open_or_close_patterns' (open_or_close_patterns' ps (CloseVar x) i)
                                     (open_with_var x)
                                     i
             == ps)
    (decreases ps)
  = match ps with
    | [] -> ()
    | (p, b)::ps' ->
      open_close_inverse'_pattern i p x;
      let n = binder_offset_pattern p in
      binder_offset_pattern_invariant p (CloseVar x) i;
      open_close_inverse'_patterns (i + n) ps' x

and open_close_inverse'_pattern (i:nat) (p:pattern{ln'_pattern p (i - 1)}) (x:var)
  : Lemma 
    (ensures open_or_close_pattern' (open_or_close_pattern' p (CloseVar x) i)
                                    (open_with_var x)
                                      i
             == p)
    (decreases p)
  = match p with
    | Pat_Constant _ -> ()

    | Pat_Cons fv us pats -> 
      open_close_inverse'_patterns i pats x
      
    | Pat_Var bv
    | Pat_Wild bv ->
      open_close_inverse'_bv i bv x

    | Pat_Dot_Term topt ->
      match topt with
      | None -> ()
      | Some t -> open_close_inverse' i t x

    
and open_close_inverse'_branch (i:nat) (br:branch{ln'_branch br (i - 1)}) (x:var)
  : Lemma
    (ensures open_or_close_branch'
                 (open_or_close_branch' br (CloseVar x) i)
                 (open_with_var x)
                 i
             == br)
    (decreases br)  
  = let p, t = br in
    let j = binder_offset_pattern p in
    binder_offset_pattern_invariant p (CloseVar x) i;
    open_close_inverse'_pattern i p x;
    open_close_inverse' (i + j) t x
  
and open_close_inverse'_branches (i:nat)
                                (brs:list branch { ln'_branches brs (i - 1) })
                                (x:var)
  : Lemma
    (ensures open_or_close_branches'
                 (open_or_close_branches' brs (CloseVar x) i)
                 (open_with_var x)
                 i
             == brs)
    (decreases brs)
  = match brs with
    | [] -> ()
    | br::brs -> 
      open_close_inverse'_branch i br x;
      open_close_inverse'_branches i brs x
  
and open_close_inverse'_match_returns (i:nat) 
                                     (m:match_returns_ascription { ln'_match_returns m (i - 1) })
                                     (x:var)
  : Lemma 
    (ensures open_or_close_match_returns' 
                 (open_or_close_match_returns' m (CloseVar x) i)
                 (open_with_var x)
                 i
             == m)
    (decreases m)
  = let b, (ret, as_, eq) = m in
    open_close_inverse'_binder i b x;
    let ret =
      match ret with
      | Inl t ->
        open_close_inverse' (i + 1) t x
      | Inr c ->
        open_close_inverse'_comp (i + 1) c x
    in
    let as_ =
      match as_ with
      | None -> ()
      | Some t ->
        open_close_inverse' (i + 1) t x
    in
    ()


let open_close_inverse (e:R.term { ln e }) (x:var)
  : Lemma (open_term (close_term e x) x == e)
   = close_term_spec e x;
     open_term_spec (close_term e x) x;
     open_close_inverse' 0 e x


////////////////////////////////////////////////////////////////////////////////
// freevars
////////////////////////////////////////////////////////////////////////////////


let rec freevars (e:term)
  : FStar.Set.set var
  = match inspect_ln e with
    | Tv_Uvar _ _ -> Set.complement Set.empty
    
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown 
    | Tv_BVar _ -> Set.empty

    | Tv_Var x -> Set.singleton (bv_index x)
       
    | Tv_App e1 (e2, _) ->
      Set.union (freevars e1) (freevars e2)

    | Tv_Abs b body -> 
      Set.union (freevars_binder b) (freevars body)

    | Tv_Arrow b c ->
      Set.union (freevars_binder b) (freevars_comp c)

    | Tv_Refine bv f ->
      Set.union (freevars_bv bv) (freevars f)
      
    | Tv_Let recf attrs bv def body ->
      freevars_terms attrs `Set.union`
      freevars_bv bv `Set.union`
      freevars def `Set.union`
      freevars body

    | Tv_Match scr ret brs ->
      freevars scr `Set.union`
      freevars_opt ret freevars_match_returns  `Set.union`
      freevars_branches brs

    | Tv_AscribedT e t tac b ->
      freevars e `Set.union`
      freevars t `Set.union`
      freevars_opt tac freevars
                            
    | Tv_AscribedC e c tac b ->
      freevars e `Set.union`
      freevars_comp c `Set.union`
      freevars_opt tac freevars

and freevars_opt (#a:Type0) (o:option a) (f: (x:a { x << o } -> FStar.Set.set var))
  : FStar.Set.set var
  = match o with
    | None -> Set.empty
    | Some x -> f x

and freevars_comp (c:comp)
  : FStar.Set.set var
  = match inspect_comp c with
    | C_Total t
    | C_GTotal t ->
      freevars t

    | C_Lemma pre post pats ->
      freevars pre `Set.union`
      freevars post `Set.union`
      freevars pats

    | C_Eff us eff_name res args decrs ->
      freevars res `Set.union`
      freevars_args args `Set.union`
      freevars_terms decrs

and freevars_args (ts:list argv)
  : FStar.Set.set var
  = match ts with
    | [] -> Set.empty
    | (t,q)::ts ->
      freevars t `Set.union`
      freevars_args ts

and freevars_terms (ts:list term)
  : FStar.Set.set var
  = match ts with
    | [] -> Set.empty
    | t::ts ->
      freevars t `Set.union`
      freevars_terms ts

and freevars_bv (b:bv)
  : Tot (Set.set var) (decreases b)
  = let bv = inspect_bv b in
    freevars bv.bv_sort
    
and freevars_binder (b:binder)
  : Tot (Set.set var) (decreases b)
  = let bndr  = inspect_binder b in
    let bv, (q, attrs) = bndr in
    freevars_bv bv `Set.union`
    freevars_terms attrs 
    

and freevars_pattern (p:pattern) 
  : Tot (Set.set var) (decreases p)
  = match p with
    | Pat_Constant _ ->
      Set.empty

    | Pat_Cons fv us pats -> 
      freevars_patterns pats
      
    | Pat_Var bv 
    | Pat_Wild bv ->
      freevars_bv bv

    | Pat_Dot_Term topt ->
      freevars_opt topt freevars

and freevars_patterns (ps:list (pattern & bool))
  : Tot (Set.set var) (decreases ps)
  = match ps with
    | [] -> Set.empty
    | (p, b)::ps ->
      freevars_pattern p `Set.union`
      freevars_patterns ps

and freevars_branch (br:branch)
  : Tot (Set.set var) (decreases br)
  = let p, t = br in
    freevars_pattern p `Set.union`
    freevars t

and freevars_branches (brs:list branch)
  : Tot (Set.set var) (decreases brs)
  = match brs with
    | [] -> Set.empty
    | hd::tl -> freevars_branch hd `Set.union` freevars_branches tl
  
and freevars_match_returns (m:match_returns_ascription)
  : Tot (Set.set var) (decreases m)
  = let b, (ret, as_, eq) = m in
    let b = freevars_binder b in
    let ret =
      match ret with
      | Inl t -> freevars t
      | Inr c -> freevars_comp c
    in
    let as_ = freevars_opt as_ freevars in
    b `Set.union` ret `Set.union` as_


let rec close_open_inverse' (i:nat)
                            (t:term) 
                            (x:var { ~(x `Set.mem` freevars t) })
  : Lemma 
       (ensures open_or_close_term' 
                       (open_or_close_term' t (open_with_var x) i)
                       (CloseVar x)
                       i
                == t)
       (decreases t)
  = match inspect_ln t with
    | Tv_Uvar _ _ -> assert false
    | Tv_UInst _ _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown
    | Tv_Var _
    | Tv_BVar _ -> ()
    | Tv_App t1 a ->
      close_open_inverse' i t1 x;
      close_open_inverse' i (fst a) x
      
    | Tv_Abs b body -> 
      close_open_inverse'_binder i b x;
      close_open_inverse' (i + 1) body x

    | Tv_Arrow b c ->
      close_open_inverse'_binder i b x;
      close_open_inverse'_comp (i + 1) c x

    | Tv_Refine bv f ->
      close_open_inverse'_bv i bv x;
      close_open_inverse' (i + 1) f x
      
    | Tv_Let recf attrs bv def body ->
      close_open_inverse'_terms i attrs x;
      close_open_inverse'_bv i bv x;
      close_open_inverse' (if recf then (i + 1) else i) def x;
      close_open_inverse' (i + 1) body x

    | Tv_Match scr ret brs ->
      close_open_inverse' i scr x;
      (match ret with
       | None -> ()
       | Some m -> close_open_inverse'_match_returns i m x);
      close_open_inverse'_branches i brs x

    | Tv_AscribedT e t tac b ->
      close_open_inverse' i e x;
      close_open_inverse' i t x;
      (match tac with
       | None -> ()
       | Some t -> close_open_inverse' i t x)

    | Tv_AscribedC e c tac b ->
      close_open_inverse' i e x;
      close_open_inverse'_comp i c x;
      (match tac with
       | None -> ()
       | Some t -> close_open_inverse' i t x)
      
and close_open_inverse'_comp (i:nat)
                             (c:comp)
                             (x:var{ ~(x `Set.mem` freevars_comp c) })
  : Lemma
       (ensures open_or_close_comp' 
                       (open_or_close_comp' c (open_with_var x) i)
                       (CloseVar x)
                       i
                == c)
       (decreases c)
   = match inspect_comp c with
    | C_Total t 
    | C_GTotal t ->    
      close_open_inverse' i t x

    | C_Lemma pre post pats ->
      close_open_inverse' i pre x;
      close_open_inverse' i post x;
      close_open_inverse' i pats x

    | C_Eff us eff_name res args decrs ->
      close_open_inverse' i res x;
      close_open_inverse'_args i args x;
      close_open_inverse'_terms i decrs x

and close_open_inverse'_args (i:nat) (args:list argv) (x:var{ ~(x `Set.mem` freevars_args args) })
  : Lemma
       (ensures open_or_close_args' 
                       (open_or_close_args' args (open_with_var x) i)
                       (CloseVar x)
                       i
                == args)
       (decreases args)
  = match args with
    | [] -> ()
    | (a, q) :: args ->
      close_open_inverse' i a x;
      close_open_inverse'_args i args x

and close_open_inverse'_binder (i:nat) (b:binder) (x:var{ ~(x `Set.mem` freevars_binder b) })
  : Lemma 
       (ensures open_or_close_binder' 
                       (open_or_close_binder' b (open_with_var x) i)
                       (CloseVar x)
                       i
                == b)
       (decreases b)
  = let bndr  = inspect_binder b in
    let bv, (q, attrs) = bndr in
    close_open_inverse'_bv i bv x;
    close_open_inverse'_terms i attrs x;
    pack_inspect_binder b

and close_open_inverse'_bv (i:nat) (bv:bv) (x:var{ ~(x `Set.mem` freevars_bv bv) })
  : Lemma 
       (ensures open_or_close_bv' 
                       (open_or_close_bv' bv (open_with_var x) i)
                       (CloseVar x)
                       i
                == bv)
       (decreases bv)
  = let bv = inspect_bv bv in
    close_open_inverse' i bv.bv_sort x

and close_open_inverse'_terms (i:nat) (ts:list term) (x:var{ ~(x `Set.mem` freevars_terms ts) })
  : Lemma 
       (ensures open_or_close_terms' 
                       (open_or_close_terms' ts (open_with_var x) i)
                       (CloseVar x)
                       i
                == ts)
       (decreases ts)
  = match ts with
    | [] -> ()
    | hd :: tl ->
      close_open_inverse' i hd x;
      close_open_inverse'_terms i tl x

and close_open_inverse'_branches (i:nat) (brs:list branch) 
                                 (x:var{ ~(x `Set.mem` freevars_branches brs) })
  : Lemma
    (ensures open_or_close_branches'
                       (open_or_close_branches' brs (open_with_var x) i)
                       (CloseVar x)
                       i
                == brs)
       (decreases brs)
  = match brs with
    | [] -> ()
    | b :: brs ->
      close_open_inverse'_branch i b x;
      close_open_inverse'_branches i brs x

and close_open_inverse'_branch (i:nat)
                               (br:branch)
                               (x:var{ ~(x `Set.mem` freevars_branch br) })
  : Lemma
    (ensures open_or_close_branch'
                       (open_or_close_branch' br (open_with_var x) i)
                       (CloseVar x)
                       i
                == br)
    (decreases br)
  = let p, t = br in
    close_open_inverse'_pattern i p x;
    binder_offset_pattern_invariant p (open_with_var x) i;
    close_open_inverse' (i + binder_offset_pattern p) t x


and close_open_inverse'_pattern (i:nat)
                                (p:pattern)
                                (x:var{ ~(x `Set.mem` freevars_pattern p) })
  : Lemma
    (ensures open_or_close_pattern'
                       (open_or_close_pattern' p (open_with_var x) i)
                       (CloseVar x)
                       i
                == p)
    (decreases p)
  = match p with
    | Pat_Constant _ -> ()

    | Pat_Cons fv us pats -> 
      close_open_inverse'_patterns i pats x
      
    | Pat_Var bv
    | Pat_Wild bv ->
      close_open_inverse'_bv i bv x

    | Pat_Dot_Term topt ->
      match topt with
      | None -> ()
      | Some t -> close_open_inverse' i t x

and close_open_inverse'_patterns (i:nat)
                                 (ps:list (pattern & bool))
                                 (x:var {~ (x `Set.mem` freevars_patterns ps) })
  : Lemma 
    (ensures open_or_close_patterns' (open_or_close_patterns' ps (open_with_var x) i)
                                     (CloseVar x)
                                     i
             == ps)
    (decreases ps)
  = match ps with
    | [] -> ()
    | (p, b)::ps' ->
      close_open_inverse'_pattern i p x;
      let n = binder_offset_pattern p in
      binder_offset_pattern_invariant p (open_with_var x) i;
      close_open_inverse'_patterns (i + n) ps' x

and close_open_inverse'_match_returns (i:nat) (m:match_returns_ascription)
                                      (x:var{ ~(x `Set.mem` freevars_match_returns m) })
  : Lemma
    (ensures open_or_close_match_returns'
                       (open_or_close_match_returns' m (open_with_var x) i)
                       (CloseVar x)
                       i
                == m)
       (decreases m)
  = let b, (ret, as_, eq) = m in
    close_open_inverse'_binder i b x;
    (match ret with
      | Inl t -> close_open_inverse' (i + 1) t x
      | Inr c -> close_open_inverse'_comp (i + 1) c x);
    (match as_ with
     | None -> ()
     | Some t -> close_open_inverse' (i + 1) t x)



let close_open_inverse (e:R.term) (x:var {~ (x `Set.mem` freevars e) })
  : Lemma (close_term (open_term e x) x == e)
   = open_term_spec e x;
     close_term_spec (open_term e x) x;
     close_open_inverse' 0 e x

//
// Type of the top-level tactic that would splice-in the definitions
//

let fstar_env_fvs (g:R.env) =
  lookup_fvar g unit_fv == Some (tm_type u_zero) /\
  lookup_fvar g bool_fv == Some (tm_type u_zero) /\
  lookup_fvar g b2t_fv  == Some b2t_ty

type fstar_env = g:R.env{fstar_env_fvs g}

type fstar_top_env = g:fstar_env {
  forall x. None? (lookup_bvar g x )
}

//
// This doesn't allow for universe polymorphic definitions
//
// May be we can change it to:
//
// g:fstar_top_env -> T.tac ((us, e, t):(univ_names & term & typ){typing (push g us) e t})
//

type dsl_tac_t = g:fstar_top_env -> T.Tac (r:(R.term & R.typ){typing g (fst r) (snd r)})


//
// THIS IS A STOPGAP
//
// Used in mini steel where we don't have implicit
//   arguments or universe instantiations
//
// And so we cannot correctly elaborate to a Prims.eq2
//   which requires both of these
//
// SHOULD GO AWAY
//
// When we add both these to mini steel syntax
//
unfold
let meq2 (a:Type0) (x y:a) : prop = Prims.eq2 x y
