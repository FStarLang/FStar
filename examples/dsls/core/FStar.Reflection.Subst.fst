module FStar.Reflection.Subst

open FStar.Reflection
module R = FStar.Reflection

open FStar.Reflection.Helpers

//replace BV 0 in t with v
noeq
type open_or_close =
  | OpenWith of term
  | CloseVar of var
  | Rename   : var -> var -> open_or_close

assume val open_or_close_ctx_uvar_and_subst (c:ctx_uvar_and_subst) (v:open_or_close) (i:nat) 
  : ctx_uvar_and_subst
  
let rec open_or_close_term' (t:term) (v:open_or_close) (i:nat)
  : GTot term (decreases t)
  = match inspect_ln t with
    | Tv_FVar _
    | Tv_UInst _ _
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
      assume (bv << t); //bug in the definition of R.smaller
      let bv' = open_or_close_bv' bv v i in
      pack_ln (Tv_Refine bv' (open_or_close_term' f v (i + 1)))

    | Tv_Uvar j c ->
      pack_ln (Tv_Uvar j (open_or_close_ctx_uvar_and_subst c v i))
      
    | Tv_Let recf attrs bv def body ->
      assume (attrs << t); //bug in defn of R.smaller
      pack_ln (Tv_Let recf 
                      (open_or_close_terms' attrs v i)
                      (open_or_close_bv' bv v i)
                      (if recf 
                       then open_or_close_term' def v (i + 1)
                       else open_or_close_term' def v i)
                      (open_or_close_term' body v (i + 1)))

    | Tv_Match scr ret brs ->
      assume (brs << t);
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
    assume (bv << b);
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
      pack_comp (C_Total (open_or_close_term' t v i)
                         u
                         (open_or_close_terms' decr v i))

    | C_GTotal t u decr ->
      pack_comp (C_GTotal (open_or_close_term' t v i)
                          u
                          (open_or_close_terms' decr v i))

    | C_Lemma pre post pats ->
      pack_comp (C_Lemma (open_or_close_term' pre v i)
                         (open_or_close_term' post v i)
                         (open_or_close_term' pats v i))

    | C_Eff us eff_name res args ->
      assume (args << c);
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

    | Pat_Cons fv pats -> 
      let pats, n = open_or_close_patterns' pats v i in
      Pat_Cons fv pats, n
      
    | Pat_Var bv ->
      Pat_Var (open_or_close_bv' bv v i), 1

    | Pat_Wild bv ->
      Pat_Wild (open_or_close_bv' bv v i), 1

    | Pat_Dot_Term bv t -> //CHECK!
      Pat_Dot_Term (open_or_close_bv' bv v i) (open_or_close_term' t v i), 0

    
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

assume val open_with (t:term) (v:term)
  : term
  
assume val open_with_spec (t v:term)
  : Lemma (open_with t v == open_or_close_term' t (OpenWith v) 0)

assume val open_comp_with (c:comp) (v:term)
  : comp
  
assume val open_comp_with_spec (c:comp) (v:term)
  : Lemma (open_comp_with c v == open_or_close_comp' c (OpenWith v) 0)

assume val open_term (t:term) (v:var) 
  : term

assume val open_term_spec (t:term) (v:var)
  : Lemma (open_term t v == open_or_close_term' t (OpenWith (var_as_term v)) 0)

assume val open_comp (c:comp) (v:var) 
  : comp

assume val open_comp_spec (c:comp) (v:var)
  : Lemma (open_comp c v == open_or_close_comp' c (OpenWith (var_as_term v)) 0)

assume val close_term (t:term) (v:var) 
  : term

assume val close_term_spec (t:term) (v:var)
  : Lemma (close_term t v == open_or_close_term' t (CloseVar v) 0)

assume val close_comp (c:comp) (v:var)
  : comp

assume val close_comp_spec (c:comp) (v:var)
  : Lemma (close_comp c v == open_or_close_comp' c (CloseVar v) 0)

assume val rename (t:term) (x y:var)
  : term

assume val rename_spec (t:term) (x y:var)
  : Lemma (rename t x y == open_or_close_term' t (Rename x y) 0)

let close_guard (g:guard) (x:var) : guard =
  match g with
  | None -> None
  | Some g -> Some (close_term g x)

let rename_bindings bs x y = FStar.List.Tot.map (fun (v, t) -> (v, rename t x y)) bs
