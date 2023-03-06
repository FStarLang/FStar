module Refl.Typing
open FStar.List.Tot
open FStar.Reflection

module R = FStar.Reflection
module T = FStar.Tactics
module FTB = FStar.Tactics.Builtins
module RTB = Refl.Typing.Builtins

let inspect_pack t = R.inspect_pack_inv t
  
let pack_inspect t = R.pack_inspect_inv t
  
let inspect_pack_bv t = admit ()
  
let pack_inspect_bv t = admit ()

let inspect_pack_binder (bv:_) = admit ()
  
let pack_inspect_binder (t:R.binder) = admit ()
  
let pack_inspect_comp (t:R.comp) = admit ()
  
let inspect_pack_comp (t:R.comp_view) = admit ()

let pack_inspect_fv (fv:R.fv) = admit ()

let inspect_pack_fv (nm:R.name) = admit ()

let pack_inspect_universe u = admit ()

let inspect_pack_universe u = admit ()

let lookup_bvar (e:env) (x:int) : option term = magic ()

let lookup_fvar_uinst (e:R.env) (x:R.fv) (us:list R.universe)
  : option R.term = magic ()

let lookup_bvar_extend_env (g:env) (x y:var) (ty:term) = admit ()

let lookup_fvar_extend_env (g:env) (x:fv) (us:universes) (y:var) (ty:term) = admit ()

let open_or_close_ctx_uvar_and_subst (c:ctx_uvar_and_subst) (v:open_or_close) (i:nat) = magic ()

let open_with (t:term) (v:term) = RTB.open_with t v
  
let open_with_spec (t v:term) = admit ()

let open_term (t:term) (v:var) = RTB.open_term t v

let open_term_spec (t:term) (v:var) = admit ()
  
let close_term (t:term) (v:var) = RTB.close_term t v

let close_term_spec (t:term) (v:var) = admit ()

let rename (t:term) (x y:var)= RTB.rename t x y

let rename_spec (t:term) (x y:var) = admit ()
  
let bv_index_of_make_bv (n:nat) (t:term) = ()

let subtyping_token_renaming (g:env)
                             (bs0:bindings)
                             (bs1:bindings)
                             (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                             (y:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) y) })
                             (t:term)
                             (t0 t1:term)
                             (d:FTB.subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1) = magic ()

let subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term)
                             (d:FTB.subtyping_token (extend_env_l g (bs1@bs0)) t0 t1) = magic ()

let well_typed_terms_are_ln (g:R.env) (e:R.term) (t:R.term) (_:typing g e t) = admit ()

let type_correctness (g:R.env) (e:R.term) (t:R.term) (_:typing g e t) = magic ()

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
    let {binder_bv=bv; binder_qual=q; binder_attrs=attrs} = bndr in
    open_close_inverse'_bv i bv x;
    open_close_inverse'_terms i attrs x;
    assert (open_or_close_bv' (open_or_close_bv' bv (CloseVar x) i) (open_with_var x) i == bv);
    assert (open_or_close_terms' (open_or_close_terms' attrs (CloseVar x) i) (open_with_var x) i == attrs);    
    pack_inspect_binder b;    
    assert (pack_binder {binder_bv=bv; binder_qual=q; binder_attrs=attrs} == b)

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
    close_open_inverse'_bv i bndr.binder_bv x;
    close_open_inverse'_terms i bndr.binder_attrs x;
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

let rec close_with_not_free_var (t:R.term) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars t)))
      (ensures open_or_close_term' t (CloseVar x) i == t) =

  match inspect_ln t with
  | Tv_Var _
  | Tv_BVar _
  | Tv_FVar _
  | Tv_UInst _ _ -> ()
  | Tv_App hd (arg, _) ->
    close_with_not_free_var hd x i;
    close_with_not_free_var arg x i
  | Tv_Abs b body ->
    close_binder_with_not_free_var b x i;
    close_with_not_free_var body x (i + 1)
  | Tv_Arrow b c ->
    close_binder_with_not_free_var b x i;
    close_comp_with_not_free_var c x (i + 1)
  | Tv_Type _ -> ()
  | Tv_Refine bv t ->
    close_bv_with_not_free_var bv x i;
    close_with_not_free_var t x (i + 1)
  | Tv_Const _ -> ()
  | Tv_Uvar _ _ -> assert False
  | Tv_Let recf attrs bv e1 e2 ->
    close_terms_with_not_free_var attrs x i;
    close_bv_with_not_free_var bv x i;
    (if recf then close_with_not_free_var e1 x (i + 1)
     else close_with_not_free_var e1 x i);
    close_with_not_free_var e2 x (i + 1)
  | Tv_Match scrutinee ret_opt brs ->
    close_with_not_free_var scrutinee x i;
    (match ret_opt with
     | None -> ()
     | Some ret -> close_match_returns_with_not_free_var ret x i);
    close_branches_with_not_free_var brs x i

  | Tv_AscribedT e t tacopt _ ->
    close_with_not_free_var e x i;
    close_with_not_free_var t x i;
    (match tacopt with
     | None -> ()
     | Some tac -> close_with_not_free_var tac x i)

  | Tv_AscribedC e c tacopt _ ->
    close_with_not_free_var e x i;
    close_comp_with_not_free_var c x i;
    (match tacopt with
     | None -> ()
     | Some tac -> close_with_not_free_var tac x i)

  | Tv_Unknown -> ()

and close_match_returns_with_not_free_var
  (r:match_returns_ascription)
  (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_match_returns r)))
      (ensures open_or_close_match_returns' r (CloseVar x) i == r) =

  let b, (ret, as_opt, _) = r in
  close_binder_with_not_free_var b x i;
  (match ret with
   | Inl t -> close_with_not_free_var t x (i + 1)
   | Inr c -> close_comp_with_not_free_var c x (i + 1));
  (match as_opt with
   | None -> ()
   | Some t -> close_with_not_free_var t x (i + 1))

and close_branches_with_not_free_var
  (brs:list R.branch)
  (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_branches brs)))
      (ensures open_or_close_branches' brs (CloseVar x) i == brs) =

  match brs with
  | [] -> ()
  | hd::tl ->
    close_branch_with_not_free_var hd x i;
    close_branches_with_not_free_var tl x i

and close_branch_with_not_free_var
  (br:R.branch)
  (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_branch br)))
      (ensures open_or_close_branch' br (CloseVar x) i == br) =

  let p, t = br in
  close_pattern_with_not_free_var p x i;
  close_with_not_free_var t x (binder_offset_pattern p + i)
  
and close_pattern_with_not_free_var (p:R.pattern) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_pattern p)))
      (ensures open_or_close_pattern' p (CloseVar x) i == p) =

  match p with
  | Pat_Constant _ -> ()
  | Pat_Cons _ _ pats ->
    close_patterns_with_not_free_var pats x i
  | Pat_Var bv
  | Pat_Wild bv -> close_bv_with_not_free_var bv x i
  | Pat_Dot_Term topt ->
    (match topt with
     | None -> ()
     | Some t -> close_with_not_free_var t x i)

and close_patterns_with_not_free_var (l:list (R.pattern & bool)) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_patterns l)))
      (ensures open_or_close_patterns' l (CloseVar x) i == l) =

  match l with
  | [] -> ()
  | (p, _)::tl ->
    close_pattern_with_not_free_var p x i;
    close_patterns_with_not_free_var tl x (binder_offset_pattern p + i)

and close_terms_with_not_free_var (l:list R.term) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_terms l)))
      (ensures open_or_close_terms' l (CloseVar x) i == l) =

  match l with
  | [] -> ()
  | hd::tl ->
    close_with_not_free_var hd x i;
    close_terms_with_not_free_var tl x i

and close_binder_with_not_free_var (b:R.binder) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_binder b)))
      (ensures open_or_close_binder' b (CloseVar x) i == b) =

  let {binder_bv; binder_attrs} = inspect_binder b in
  close_bv_with_not_free_var binder_bv x i;
  close_terms_with_not_free_var binder_attrs x i

and close_bv_with_not_free_var (b:R.bv) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_bv b)))
      (ensures open_or_close_bv' b (CloseVar x) i == b) =

  let {bv_sort} = inspect_bv b in
  close_with_not_free_var bv_sort x i

and close_comp_with_not_free_var (c:R.comp) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_comp c)))
      (ensures open_or_close_comp' c (CloseVar x) i == c) =

  match inspect_comp c with
  | C_Total t
  | C_GTotal t -> close_with_not_free_var t x i
  | C_Lemma pre post pats ->
    close_with_not_free_var pre x i;
    close_with_not_free_var post x i;
    close_with_not_free_var pats x i
  | C_Eff _ _ t args decrs ->
    close_with_not_free_var t x i;
    close_args_with_not_free_var args x i;
    close_terms_with_not_free_var decrs x i

and close_args_with_not_free_var (l:list R.argv) (x:var) (i:nat)
  : Lemma
      (requires ~ (Set.mem x (freevars_args l)))
      (ensures open_or_close_args' l (CloseVar x) i == l) =

  match l with
  | [] -> ()
  | (t, _)::tl ->
    close_with_not_free_var t x i;
    close_args_with_not_free_var tl x i

let beta_reduction _ _ _ _ = admit ()
