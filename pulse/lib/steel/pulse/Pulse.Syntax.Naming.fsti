module Pulse.Syntax.Naming
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
open FStar.List.Tot
module T = FStar.Tactics
module E = Pulse.Elaborate.Pure
open Pulse.Syntax


let rec freevars (t:term) 
  : Set.set var
  = match t with
    | Tm_BVar _
    | Tm_FVar  _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Emp
    | Tm_Type _
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_UVar _
    | Tm_Unknown -> Set.empty
    | Tm_Var nm -> Set.singleton nm.nm_index
    | Tm_Refine b body ->
      Set.union (freevars b.binder_ty) (freevars body)
    | Tm_PureApp t1 _ t2
    | Tm_Star  t1 t2
    | Tm_ExistsSL _ t1 t2 _
    | Tm_ForallSL _ t1 t2 ->
      Set.union (freevars t1) (freevars t2)
    | Tm_Let t e1 e2 ->
      Set.union (Set.union (freevars t) (freevars e1)) (freevars e2)
    | Tm_Pure p -> freevars p
    | Tm_FStar t -> RT.freevars t
    | Tm_Arrow b _ body -> Set.union (freevars b.binder_ty) (freevars_comp body)
  
and freevars_comp (c:comp) : Set.set var =
  match c with
  | C_Tot t -> freevars t
  | C_ST s -> freevars_st_comp s
  | C_STAtomic inames s
  | C_STGhost inames s ->
    freevars inames `Set.union` freevars_st_comp s

and freevars_st_comp (s:st_comp) : Set.set var =
  freevars s.res `Set.union`
  freevars s.pre `Set.union`
  freevars s.post

let freevars_opt (t:option term) : Set.set var =
  match t with
  | None -> Set.empty
  | Some t -> freevars t

let rec freevars_list (t:list term) : Set.set var =
  match t with
  | [] -> Set.empty
  | hd::tl -> freevars hd `Set.union` freevars_list tl

let rec freevars_st (t:st_term)
  : Set.set var
  = match t.term with
    | Tm_Return { term } ->
      freevars term
    | Tm_Abs { b; pre; body; post } ->
      Set.union (freevars b.binder_ty) 
                (Set.union (freevars_st body)
                           (Set.union (freevars_opt pre)
                                      (freevars_opt post)))
    | Tm_STApp { head; arg } ->
      Set.union (freevars head) (freevars arg)
    | Tm_Bind { binder; head; body } ->
      Set.union 
        (Set.union (freevars binder.binder_ty) 
                   (freevars_st head))
        (freevars_st body)
    | Tm_TotBind { head; body } ->
      Set.union (freevars head) (freevars_st body)
    | Tm_If { b; then_; else_; post } ->
      Set.union (Set.union (freevars b) (freevars_st then_))
                (Set.union (freevars_st else_) (freevars_opt post))
    | Tm_ElimExists { p } ->
      freevars p
    | Tm_IntroExists { p; witnesses } ->
      Set.union (freevars p) (freevars_list witnesses)
    | Tm_While { invariant; condition; body } ->
      Set.union (freevars invariant)
                (Set.union (freevars_st condition)
                           (freevars_st body))
    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      Set.union
        (Set.union (freevars pre1)
                   (Set.union (freevars_st body1)
                              (freevars post1)))
        (Set.union (freevars pre2)
                   (Set.union (freevars_st body2)
                              (freevars post2)))

    | Tm_WithLocal { initializer; body } ->
      Set.union (freevars initializer)
                (freevars_st body)

    | Tm_Rewrite { t1; t2 } ->
      Set.union (freevars t1) (freevars t2)

    | Tm_Admit { typ; post } ->
      Set.union (freevars typ)
                (freevars_opt post)

    | Tm_Protect { t } -> freevars_st t

let rec ln' (t:term) (i:int) : Tot bool (decreases t) =
  match t with
  | Tm_BVar {bv_index=j} -> j <= i
  | Tm_Var _
  | Tm_FVar _
  | Tm_UInst _ _
  | Tm_Constant _  
  | Tm_Emp
  | Tm_Type _
  | Tm_VProp
  | Tm_Inames
  | Tm_EmpInames
  | Tm_UVar _
  | Tm_Unknown -> true

  | Tm_Refine b phi ->
    ln' b.binder_ty i &&
    ln' phi (i + 1)

  | Tm_PureApp t1 _ t2
  | Tm_Star t1 t2 ->
    ln' t1 i &&
    ln' t2 i


  | Tm_Let t e1 e2 ->
    ln' t i &&
    ln' e1 i &&
    ln' e2 (i + 1)

  | Tm_Pure p ->
    ln' p i

  | Tm_ExistsSL _ t body _
  | Tm_ForallSL _ t body ->
    ln' t i &&
    ln' body (i + 1)
    
  | Tm_Arrow b _ c ->
    ln' b.binder_ty i &&
    ln_c' c (i + 1)
    
  | Tm_FStar t ->
    RT.ln' t i

and ln_c' (c:comp) (i:int)
  : Tot bool (decreases c)
  = match c with
    | C_Tot t -> ln' t i
    | C_ST s -> ln_st_comp s i
    | C_STAtomic inames s
    | C_STGhost inames s ->
      ln' inames i &&
      ln_st_comp s i

and ln_st_comp (s:st_comp) (i:int) : Tot bool (decreases s) =
  ln' s.res i &&
  ln' s.pre i &&
  ln' s.post (i + 1) (* post has 1 impliict abstraction *)

let ln_opt' (t:option term) (i:int) : bool =
  match t with
  | None -> true
  | Some t -> ln' t i

let rec ln_list' (t:list term) (i:int) : bool =
  match t with
  | [] -> true
  | hd::tl -> ln' hd i && ln_list' tl i

let rec ln_st' (t:st_term) (i:int)
  : Tot bool (decreases t)
  = match t.term with
    | Tm_Return { term } ->
      ln' term i
      
    | Tm_Abs { b; pre; body; post } ->
      ln' b.binder_ty i &&
      ln_st' body (i + 1) &&
      ln_opt' pre (i + 1) &&
      ln_opt' post (i + 2)
  
    | Tm_STApp { head; arg } ->
      ln' head i &&
      ln' arg i

    | Tm_Bind { binder; head; body } ->
      ln' binder.binder_ty i &&
      ln_st' head i &&
      ln_st' body (i + 1)

    | Tm_TotBind { head; body } ->
      ln' head i &&
      ln_st' body (i + 1)

    | Tm_If { b; then_; else_; post } ->
      ln' b i &&
      ln_st' then_ i &&
      ln_st' else_ i &&
      ln_opt' post (i + 1)
  
    | Tm_ElimExists { p } ->
      ln' p i

    | Tm_IntroExists { p; witnesses } ->
      ln' p i &&
      ln_list' witnesses i
  
    | Tm_While { invariant; condition; body } ->
      ln' invariant (i + 1) &&
      ln_st' condition i &&
      ln_st' body i

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      ln' pre1 i &&
      ln_st' body1 i &&
      ln' post1 (i + 1) &&
      ln' pre2 i &&
      ln_st' body2 i &&
      ln' post2 (i + 1)

    | Tm_WithLocal { initializer; body } ->
      ln' initializer i &&
      ln_st' body (i + 1)

    | Tm_Rewrite { t1; t2 } ->
      ln' t1 i &&
      ln' t2 i

    | Tm_Admit { typ; post } ->
      ln' typ i &&
      ln_opt' post (i + 1)

    | Tm_Protect { t } ->
      ln_st' t i

let ln (t:term) = ln' t (-1)
let ln_st (t:st_term) = ln_st' t (-1)
let ln_c (c:comp) = ln_c' c (-1)

let open_or_close_host_term (t:host_term) (v:term) (i:index)
  : Lemma (not_tv_unknown (RT.open_or_close_term' t (RT.OpenWith (E.elab_term v)) i))
  = admit()

let rec open_term' (t:term) (v:term) (i:index)
  : Tot term (decreases t)
  = match t with
    | Tm_BVar bv ->
      if i = bv.bv_index
      then v
      else t
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Emp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_UVar _
    | Tm_Unknown -> t

    | Tm_Refine b phi ->
      Tm_Refine {b with binder_ty=open_term' b.binder_ty v i}
                (open_term' phi v (i + 1))


    | Tm_PureApp head q arg ->
      Tm_PureApp (open_term' head v i) q
                 (open_term' arg v i)
                 
    | Tm_Let t e1 e2 ->
      Tm_Let (open_term' t v i)
             (open_term' e1 v i)
             (open_term' e2 v (i + 1))
             

    | Tm_Pure p ->
      Tm_Pure (open_term' p v i)
      
    | Tm_Star l r ->
      Tm_Star (open_term' l v i)
              (open_term' r v i)
              
    | Tm_ExistsSL u t body se ->
      Tm_ExistsSL u (open_term' t v i)
                    (open_term' body v (i + 1))
                    se
                  
    | Tm_ForallSL u t body ->
      Tm_ForallSL u (open_term' t v i)
                    (open_term' body v (i + 1))
    
    | Tm_Arrow b q c ->
      Tm_Arrow {b with binder_ty=open_term' b.binder_ty v i} q
               (open_comp' c v (i + 1))
  
    | Tm_FStar t ->
      open_or_close_host_term t v i;
      Tm_FStar (RT.open_or_close_term' t (RT.OpenWith (E.elab_term v)) i)

and open_comp' (c:comp) (v:term) (i:index)
  : Tot comp (decreases c)
  = match c with
    | C_Tot t ->
      C_Tot (open_term' t v i)

    | C_ST s -> C_ST (open_st_comp' s v i)

    | C_STAtomic inames s ->
      C_STAtomic (open_term' inames v i)
                 (open_st_comp' s v i)

    | C_STGhost inames s ->
      C_STGhost (open_term' inames v i)
                (open_st_comp' s v i)

and open_st_comp' (s:st_comp) (v:term) (i:index)
  : Tot st_comp (decreases s) =

  { s with res = open_term' s.res v i;
           pre = open_term' s.pre v i;
           post = open_term' s.post v (i + 1) }

let open_term_opt' (t:option term) (v:term) (i:index)
  : Tot (option term)
  = match t with
    | None -> None
    | Some t -> Some (open_term' t v i)


let rec open_term_list' (t:list term) (v:term) (i:index)
  : Tot (list term)
  = match t with
    | [] -> []
    | hd::tl -> open_term' hd v i :: open_term_list' tl v i

let open_binder b v i = 
  {b with binder_ty=open_term' b.binder_ty v i}
             
let rec open_st_term' (t:st_term) (v:term) (i:index)
  : Tot st_term (decreases t)
  = let t' =
    match t.term with
    | Tm_Return { ctag; insert_eq; term } ->
      Tm_Return { ctag; insert_eq; term=open_term' term v i }

    | Tm_Abs { b; q; pre; body; post } ->
      Tm_Abs { b=open_binder b v i;
               q;
               pre=open_term_opt' pre v (i + 1);
               body=open_st_term' body v (i + 1);
               post=open_term_opt' post v (i + 2) }

    | Tm_STApp { head; arg_qual; arg } ->
      Tm_STApp { head = open_term' head v i;
                 arg_qual;
                 arg=open_term' arg v i }

    | Tm_Bind { binder; head; body } ->
      Tm_Bind { binder = open_binder binder v i;
                head = open_st_term' head v i;
                body = open_st_term' body v (i + 1) }

    | Tm_TotBind { head; body } ->
      Tm_TotBind { head = open_term' head v i; 
                   body = open_st_term' body v (i + 1) }

    | Tm_If { b; then_; else_; post } ->
      Tm_If { b = open_term' b v i;
              then_ = open_st_term' then_ v i;
              else_ = open_st_term' else_ v i;
              post = open_term_opt' post v (i + 1) }

    | Tm_ElimExists { p } ->
      Tm_ElimExists { p = open_term' p v i }
      
    | Tm_IntroExists { erased; p; witnesses } ->
      Tm_IntroExists { erased; 
                       p = open_term' p v i;
                       witnesses = open_term_list' witnesses v i }                             

    | Tm_While { invariant; condition; body } ->
      Tm_While { invariant = open_term' invariant v (i + 1);
                 condition = open_st_term' condition v i;
                 body = open_st_term' body v i }

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      Tm_Par { pre1=open_term' pre1 v i;
               body1=open_st_term' body1 v i;
               post1=open_term' post1 v (i + 1);
               pre2=open_term' pre2 v i;
               body2=open_st_term' body2 v i;
               post2=open_term' post2 v (i + 1) }

    | Tm_WithLocal { initializer; body } ->
      Tm_WithLocal { initializer = open_term' initializer v i;
                     body = open_st_term' body v (i + 1) }

    | Tm_Rewrite { t1; t2 } ->
      Tm_Rewrite { t1 = open_term' t1 v i;
                   t2 = open_term' t2 v i }

    | Tm_Admit { ctag; u; typ; post } ->
      Tm_Admit { ctag;
                 u; 
                 typ=open_term' typ v i;
                 post=open_term_opt' post v (i + 1) }

    | Tm_Protect { t } ->
      Tm_Protect { t = open_st_term' t v i }
    in
    { t with term = t' }

let open_term_nv t nv =
    open_term' t (term_of_nvar nv) 0

// Can use this no-name version in specs only
let open_term t v : GTot term =
    open_term_nv t (v_as_nv v)

let open_st_term_nv t nv =
    open_st_term' t (term_of_nvar nv) 0

// Can use this no-name version in specs only
let open_st_term t v : GTot st_term =
    open_st_term_nv t (v_as_nv v)

let open_comp_with (c:comp) (x:term) = open_comp' c x 0

let rec close_term' (t:term) (v:var) (i:index)
  : Tot term (decreases t)
  = match t with
    | Tm_Var nm ->
      if nm.nm_index = v
      then Tm_BVar {bv_index=i;bv_ppname=nm.nm_ppname;bv_range=nm.nm_range}
      else t
    
    | Tm_BVar _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Emp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_UVar _
    | Tm_Unknown -> t

    | Tm_Refine b phi ->
      Tm_Refine {b with binder_ty=close_term' b.binder_ty v i}
                (close_term' phi v (i + 1))

    | Tm_PureApp head q arg ->
      Tm_PureApp (close_term' head v i) q
                 (close_term' arg v i)
                 
    | Tm_Let t e1 e2 ->
      Tm_Let (close_term' t v i)
             (close_term' e1 v i)
             (close_term' e2 v (i + 1))

    | Tm_Pure p ->
      Tm_Pure (close_term' p v i)
      
    | Tm_Star l r ->
      Tm_Star (close_term' l v i)
              (close_term' r v i)
              
    | Tm_ExistsSL u t body se ->
      Tm_ExistsSL u (close_term' t v i)
                    (close_term' body v (i + 1))
                    se
                  
    | Tm_ForallSL u t body ->
      Tm_ForallSL u (close_term' t v i)
                    (close_term' body v (i + 1))
    
    | Tm_Arrow b q c ->
      Tm_Arrow {b with binder_ty=close_term' b.binder_ty v i} q
               (close_comp' c v (i + 1))

    | Tm_FStar t ->
      Tm_FStar (RT.open_or_close_term' t (RT.CloseVar v) i)

and close_comp' (c:comp) (v:var) (i:index)
  : Tot comp (decreases c)
  = match c with
    | C_Tot t ->
      C_Tot (close_term' t v i)

    | C_ST s -> C_ST (close_st_comp' s v i)

    | C_STAtomic inames s ->
      C_STAtomic (close_term' inames v i)
                 (close_st_comp' s v i)

    | C_STGhost inames s ->
      C_STGhost (close_term' inames v i)
                (close_st_comp' s v i)

and close_st_comp' (s:st_comp) (v:var) (i:index)
  : Tot st_comp (decreases s) =

  { s with res = close_term' s.res v i;
           pre = close_term' s.pre v i;
           post = close_term' s.post v (i + 1) }

let close_term_opt' (t:option term) (v:var) (i:index)
  : Tot (option term)
  = match t with
    | None -> None
    | Some t -> Some (close_term' t v i)


let rec close_term_list' (t:list term) (v:var) (i:index)
  : Tot (list term)
  = match t with
    | [] -> []
    | hd::tl -> close_term' hd v i :: close_term_list' tl v i

let close_binder b v i =
  {b with binder_ty=close_term' b.binder_ty v i}
             
let rec close_st_term' (t:st_term) (v:var) (i:index)
  : Tot st_term (decreases t)
  = let t' = 
    match t.term with
    | Tm_Return { ctag; insert_eq; term } ->
      Tm_Return { ctag; insert_eq; term=close_term' term v i }

    | Tm_Abs { b; q; pre; body; post } ->
      Tm_Abs { b = close_binder b v i;
               q;
               pre=close_term_opt' pre v (i + 1);
               body=close_st_term' body v (i + 1);
               post=close_term_opt' post v (i + 2) }

    | Tm_STApp { head; arg_qual; arg } ->
      Tm_STApp { head = close_term' head v i;
                 arg_qual;
                 arg = close_term' arg v i }

    | Tm_Bind { binder; head; body } ->
      Tm_Bind { binder = close_binder binder v i;
                head = close_st_term' head v i;
                body = close_st_term' body v (i + 1) }

    | Tm_TotBind { head; body } ->
      Tm_TotBind { head = close_term' head v i;
                   body = close_st_term' body v (i + 1) }

    | Tm_If { b; then_; else_; post } ->
      Tm_If { b = close_term' b v i;
              then_ = close_st_term' then_ v i;
              else_ = close_st_term' else_ v i;
              post = close_term_opt' post v (i + 1) }

    | Tm_ElimExists { p } ->
      Tm_ElimExists { p = close_term' p v i }
      
    | Tm_IntroExists { erased; p; witnesses } ->
      Tm_IntroExists { erased;
                       p = close_term' p v i;
                       witnesses = close_term_list' witnesses v i }

    | Tm_While { invariant; condition; body } ->
      Tm_While { invariant = close_term' invariant v (i + 1);
                 condition = close_st_term' condition v i;
                 body = close_st_term' body v i }

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      Tm_Par { pre1 = close_term' pre1 v i;
               body1 = close_st_term' body1 v i;
               post1 = close_term' post1 v (i + 1);
               pre2 = close_term' pre2 v i;
               body2 = close_st_term' body2 v i;
               post2 = close_term' post2 v (i + 1) }

    | Tm_WithLocal { initializer; body } ->
      Tm_WithLocal { initializer = close_term' initializer v i;
                     body = close_st_term' body v (i + 1) }

    | Tm_Rewrite { t1; t2 } ->
      Tm_Rewrite { t1 = close_term' t1 v i;
                   t2 = close_term' t2 v i }

    | Tm_Admit { ctag; u; typ; post } ->
      Tm_Admit { ctag;
                 u;
                 typ = close_term' typ v i;
                 post = close_term_opt' post v (i + 1) }

    | Tm_Protect { t } ->
      Tm_Protect { t = close_st_term' t v i }
    in
    { t with term = t' }
      
let close_term t v = close_term' t v 0
let close_st_term t v = close_st_term' t v 0
let close_comp t v = close_comp' t v 0

val close_open_inverse' (t:term) 
                        (x:var { ~(x `Set.mem` freevars t) } )
                        (i:index)
  : Lemma (ensures close_term' (open_term' t (term_of_no_name_var x) i) x i == t)

val close_open_inverse_comp' (c:comp)
                             (x:var { ~(x `Set.mem` freevars_comp c) } )
                             (i:index)
  : Lemma (ensures close_comp' (open_comp' c (term_of_no_name_var x) i) x i == c)

val close_open_inverse_opt' (t:option term)
                            (x:var { ~(x `Set.mem` freevars_opt t) })
                            (i:index)
  : Lemma (ensures close_term_opt' (open_term_opt' t (term_of_no_name_var x) i) x i == t)

val close_open_inverse_list' (t:list term)
                             (x:var { ~(x `Set.mem` freevars_list t) })
                             (i:index)
  : Lemma (ensures close_term_list' (open_term_list' t (term_of_no_name_var x) i) x i == t)

val close_open_inverse_st' (t:st_term) 
                           (x:var { ~(x `Set.mem` freevars_st t) } )
                           (i:index)
  : Lemma (ensures close_st_term' (open_st_term' t (term_of_no_name_var x) i) x i == t)

val close_open_inverse (t:term) (x:var { ~(x `Set.mem` freevars t) } )
  : Lemma (ensures close_term (open_term t x) x == t)
          (decreases t)

val close_open_inverse_st (t:st_term) (x:var { ~(x `Set.mem` freevars_st t) } )
  : Lemma (ensures close_st_term (open_st_term t x) x == t)
          (decreases t)

val open_with_gt_ln (e:term) (i:int) (t:term) (j:nat)
  : Lemma
      (requires ln' e i /\ i < j)
      (ensures open_term' e t j == e)

val open_with_gt_ln_comp (c:comp) (i:int) (t:term) (j:nat)
  : Lemma (requires ln_c' c i /\ i < j)
          (ensures open_comp' c t j == c)

val open_with_gt_ln_st (s:st_comp) (i:int) (t:term) (j:nat)
  : Lemma (requires ln_st_comp s i /\ i < j)
          (ensures open_st_comp' s t j == s)

val close_with_non_freevar (e:term) (x:var) (i:nat)
  : Lemma
      (requires ~ (x `Set.mem` freevars e))
      (ensures close_term' e x i == e)

val close_comp_with_non_free_var (c:comp) (x:var) (i:nat)
  : Lemma
    (requires ~ (x `Set.mem` freevars_comp c))
    (ensures close_comp' c x i == c)

val close_with_non_freevar_st (s:st_comp) (x:var) (i:nat)
  : Lemma
    (requires ~ (x `Set.mem` freevars_st_comp s))
    (ensures close_st_comp' s x i == s)
