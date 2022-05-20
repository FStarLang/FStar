module Refl.Typing
open FStar.Reflection

val lookup_bvar (e:env) (x:int) : option term

val lookup_fvar (e:env) (x:fv) : option term

val extend_env (e:env) (x:var) (ty:term) : env

let lookup_bvar_extend_env (g:env) (x y:var) (ty:term)
  : Lemma 
    (ensures (
           if x = y
           then lookup_bvar (extend_env g x ty) y == Some ty
           else lookup_bvar (extend_env g x ty) y == lookup_bvar g y))
    [SMTPat (lookup_bvar (extend_env g x ty) y)]
  = admit()

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
  = admit()          

//replace BV 0 in t with v
val open_ctx_uvar_and_subst (c:ctx_uvar_and_subst) (v:term) (i:nat) 
  : ctx_uvar_and_subst

noeq
type open_or_close =
  | Open of term
  | Close of var
  
let rec open_term' (t:term) (v:term) (i:nat)
  : GTot term (decreases t)
  = match inspect_ln t with
    | Tv_Var _
    | Tv_FVar _
    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown -> t
    | Tv_BVar j -> 
      if i=bv_index j 
      then v
      else t
      
    | Tv_App hd argv ->
      pack_ln (Tv_App (open_term' hd v i)
                      (open_term' (fst argv) v i, snd argv))

    | Tv_Abs b body -> 
      let b' = open_binder' b v i in
      pack_ln (Tv_Abs b' (open_term' body v (i + 1)))

    | Tv_Arrow b c ->
      let b' = open_binder' b v i in
      pack_ln (Tv_Arrow b' (open_comp' c v (i + 1)))      

    | Tv_Refine bv f ->
      assume (bv << t); //bug in the definition of R.smaller
      let bv' = open_bv' bv v i in
      pack_ln (Tv_Refine bv' (open_term' f v (i + 1)))

    | Tv_Uvar j c ->
      pack_ln (Tv_Uvar j (open_ctx_uvar_and_subst c v i))
      
    | Tv_Let recf attrs bv def body ->
      assume (attrs << t); //bug in defn of R.smaller
      pack_ln (Tv_Let recf 
                      (open_terms' attrs v i)
                      (open_bv' bv v i)
                      (if recf 
                       then open_term' def v (i + 1)
                       else open_term' def v i)
                      (open_term' body v (i + 1)))

    | Tv_Match scr ret brs ->
      assume (brs << t);
      pack_ln (Tv_Match (open_term' scr v i)
                        (match ret with
                         | None -> None
                         | Some m -> Some (open_match_returns' m v i))
                        (open_branches' brs v i))
      
    | Tv_AscribedT e t tac b ->
      pack_ln (Tv_AscribedT (open_term' e v i)
                            (open_term' t v i)
                            (match tac with
                             | None -> None
                             | Some tac -> Some (open_term' tac v i))
                             b)

    | Tv_AscribedC e c tac b ->
      pack_ln (Tv_AscribedC (open_term' e v i)
                            (open_comp' c v i)
                            (match tac with
                             | None -> None
                             | Some tac -> Some (open_term' tac v i))
                             b)

and open_bv' (b:bv) (v:term) (i:nat)
  : GTot bv (decreases b)
  = let bv = inspect_bv b in
    assume (bv << b);
    pack_bv ({bv with bv_sort = open_term' bv.bv_sort v i})

and open_binder' (b:binder) (v:term) (i:nat)
  : GTot binder (decreases b)
  = let bndr  = inspect_binder b in
    assume (bndr << b);
    let bv, (q, attrs) = bndr in
    pack_binder (open_bv' bv v i) 
                q
                (open_terms' attrs v i)

and open_comp' (c:comp) (v:term) (i:nat)
  : GTot comp (decreases c)
  = match inspect_comp c with
    | C_Total t decr ->
      pack_comp (C_Total (open_term' t v i)
                         (open_terms' decr v i))

    | C_GTotal t decr ->
      pack_comp (C_GTotal (open_term' t v i)
                          (open_terms' decr v i))

    | C_Lemma pre post pats ->
      pack_comp (C_Lemma (open_term' pre v i)
                         (open_term' post v i)
                         (open_term' pats v i))

    | C_Eff us eff_name res args ->
      assume (args << c);
      pack_comp (C_Eff us eff_name
                       (open_term' res v i)
                       (open_args' args v i))

and open_terms' (ts:list term) (v:term) (i:nat)
  : GTot (list term) (decreases ts)
  = match ts with
    | [] -> []
    | t::ts -> open_term' t v i :: open_terms' ts v i

and open_args' (ts:list argv) (v:term) (i:nat)
  : GTot (list argv) (decreases ts)
  = match ts with
    | [] -> []
    | (t,q)::ts -> (open_term' t v i,q) :: open_args' ts v i

and open_patterns' (ps:list (pattern & bool)) (v:term) (i:nat) 
  : GTot (list (pattern & bool) & nat)
         (decreases ps)
  = match ps with
    | [] -> ps, 0
    | (p, b)::ps ->
      let (p, n) = open_pattern' p v i in
      let (ps, m) = open_patterns' ps v (i + n) in
      (p,b)::ps, n + m

and open_pattern' (p:pattern) (v:term) (i:nat) 
  : GTot (pattern & nat)
         (decreases p)
  = match p with
    | Pat_Constant _ -> p,0

    | Pat_Cons fv pats -> 
      let pats, n = open_patterns' pats v i in
      Pat_Cons fv pats, n
      
    | Pat_Var bv ->
      Pat_Var (open_bv' bv v i), 1

    | Pat_Wild bv ->
      Pat_Wild (open_bv' bv v i), 1

    | Pat_Dot_Term bv t -> //CHECK!
      Pat_Dot_Term (open_bv' bv v i) (open_term' t v i), 0

    
and open_branch' (br:branch) (v:term) (i:nat)
  : GTot branch (decreases br)
  = let p, t = br in
    let p, j = open_pattern' p v i in
    let t = open_term' t v (i + j) in
    p, t
  
and open_branches' (brs:list branch) (v:term) (i:nat)
  : GTot (list branch) (decreases brs)
  = match brs with
    | [] -> []
    | br::brs -> open_branch' br v i :: open_branches' brs v i
  
and open_match_returns' (m:match_returns_ascription) (v:term) (i:nat)
  : GTot match_returns_ascription (decreases m)
  = let b, (ret, as_, eq) = m in
    let b = open_binder' b v i in
    let ret =
      match ret with
      | Inl t -> Inl (open_term' t v (i + 1))
      | Inr c -> Inr (open_comp' c v (i + 1))
    in
    let as_ =
      match as_ with
      | None -> None
      | Some t -> Some (open_term' t v (i + 1))
    in
    b, (ret, as_, eq)


val open_term_with (t:term) (v:term) : t':term { t' == open_term' t v 0 }
let make_bv (n:nat) (t:term) = { bv_ppname = "_"; bv_index = n; bv_sort = t}
let var_as_term (v:var) = pack_ln (Tv_Var (pack_bv (make_bv v (pack_ln Tv_Unknown))))

val open_term (t:term) (v:var) : t':term { t' == open_term' t (var_as_term v) 0 }
val close_term (t:term) (v:var) : term









let bv_as_binder bv = pack_binder bv Q_Explicit []

let bv_index_of_make_bv (n:nat) (t:term)
  : Lemma (ensures bv_index (pack_bv (make_bv n t)) == n)
          [SMTPat (bv_index (pack_bv (make_bv n t)))]
  = admit()

let constant_as_term (v:vconst) = pack_ln (Tv_Const v)
let unit_exp = constant_as_term C_Unit
let unit_fv = pack_fv unit_lid
let unit_ty = pack_ln (Tv_FVar unit_fv)
let bool_fv = pack_fv bool_lid
let bool_ty = pack_ln (Tv_FVar bool_fv)

let mk_total t = pack_comp (C_Total t [])
let tm_type = pack_ln (Tv_Type ())

let true_bool = pack_ln (Tv_Const C_True)
let false_bool = pack_ln (Tv_Const C_False)
val eq2 (t v0 v1:term) : term 
noeq
type constant_typing: vconst -> term -> Type0 = 
  | CT_Unit: constant_typing C_Unit unit_ty
  | CT_True: constant_typing C_True bool_ty
  | CT_False: constant_typing C_False bool_ty  
  

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
     typing g ty tm_type ->
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
     typing g e1 (pack_ln (Tv_Arrow x (pack_comp (C_Total t [])))) ->
     typing g e2 (binder_sort x) ->
     typing g (pack_ln (Tv_App e1 (e2, Q_Explicit)))
              (open_with t e2)

  | T_Arrow:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->
     t1:term ->
     t2:term ->
     typing g t1 tm_type ->
     typing (extend_env g x t1) (open_term t2 x) tm_type ->
     typing g (pack_ln (Tv_Arrow (as_binder 0 t1) (mk_total t2))) tm_type

  | T_Refine:
     g:env ->
     x:var { None? (lookup_bvar g x) } ->     
     t:term ->
     e:term ->
     typing g t tm_type ->
     typing (extend_env g x t) (open_term e x) tm_type ->
     typing g (pack_ln (Tv_Refine (pack_bv (make_bv 0 t)) e)) tm_type

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

  | ST_RefineLeft:
  
and branches_typing : env -> term -> term -> list branch -> term -> Type0 =
