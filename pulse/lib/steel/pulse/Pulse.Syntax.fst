module Pulse.Syntax
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module T = FStar.Tactics

let rec close_open_inverse' (t:term) 
                            (x:var { ~(x `Set.mem` freevars t) } )
                            (i:index)
  : Lemma (ensures close_term' (open_term' t (term_of_var x) i) x i == t)
          (decreases t)
  = match t with
    | Tm_BVar _
    | Tm_Var _
    | Tm_FVar _
    | Tm_UInst  _ _
    | Tm_Constant _
    | Tm_Emp
    | Tm_VProp
    | Tm_Type _
    | Tm_Inames 
    | Tm_EmpInames
    | Tm_UVar _
    | Tm_Unknown -> ()
    
    | Tm_Pure p ->
      close_open_inverse' p x i

    | Tm_Refine b t ->
      close_open_inverse' b.binder_ty x i;
      close_open_inverse' t x (i + 1)
          
    | Tm_PureApp l _ r
    | Tm_Star l r ->
      close_open_inverse' l x i;
      close_open_inverse' r x i

    | Tm_Let t e1 e2 ->
      close_open_inverse' t x i;    
      close_open_inverse' e1 x i;
      close_open_inverse' e2 x (i + 1)

    | Tm_ExistsSL _ t b _
    | Tm_ForallSL _ t b ->
      close_open_inverse' t x i;    
      close_open_inverse' b x (i + 1)

    | Tm_Arrow b _ body ->
      close_open_inverse' b.binder_ty x i;
      close_open_inverse_comp' body x (i + 1)

and close_open_inverse_comp' (c:comp)
                             (x:var { ~(x `Set.mem` freevars_comp c) } )
                             (i:index)
  : Lemma (ensures close_comp' (open_comp' c (term_of_var x) i) x i == c)
          (decreases c)
  = match c with
    | C_Tot t ->
      close_open_inverse' t x i

    | C_ST s ->
      close_open_inverse' s.res x i;
      close_open_inverse' s.pre x i;      
      close_open_inverse' s.post x (i + 1)

    | C_STAtomic n s
    | C_STGhost n s ->    
      close_open_inverse' n x i;    
      close_open_inverse' s.res x i;
      close_open_inverse' s.pre x i;      
      close_open_inverse' s.post x (i + 1)

let close_open_inverse_opt' (t:option term)
                            (x:var { ~(x `Set.mem` freevars_opt t) })
                            (i:index)
  : Lemma (ensures close_term_opt' (open_term_opt' t (term_of_var x) i) x i == t)
  = match t with
    | None -> ()
    | Some t -> close_open_inverse' t x i


let rec close_open_inverse_list' (t:list term)
                                 (x:var { ~(x `Set.mem` freevars_list t) })
                                 (i:index)
  : Lemma (ensures close_term_list' (open_term_list' t (term_of_var x) i) x i == t)
  = match t with
    | [] -> ()
    | hd::tl ->
      close_open_inverse' hd x i;
      close_open_inverse_list' tl x i


let rec close_open_inverse_st'  (t:st_term) 
                                (x:var { ~(x `Set.mem` freevars_st t) } )
                                (i:index)
  : Lemma (ensures close_st_term' (open_st_term' t (term_of_var x) i) x i == t)
          (decreases t)
  = match t with
    | Tm_Return _ _ t ->
      close_open_inverse' t x i

    | Tm_ElimExists p ->
      close_open_inverse' p x i    

    | Tm_Abs b _q pre body post ->
      close_open_inverse' b.binder_ty x i;
      close_open_inverse_st' body x (i + 1);
      close_open_inverse_opt' pre x (i + 1);
      close_open_inverse_opt' post x (i + 2)

    | Tm_Bind e1 e2 ->
      close_open_inverse_st' e1 x i;
      close_open_inverse_st' e2 x (i + 1)

    | Tm_STApp l _ r ->
      close_open_inverse' l x i;
      close_open_inverse' r x i
    
    | Tm_IntroExists _ p l ->
      close_open_inverse' p x i;
      close_open_inverse_list' l x i
    
    | Tm_ElimExists t ->
      close_open_inverse' t x i
      
    | Tm_While inv cond body ->
      close_open_inverse' inv x (i + 1);
      close_open_inverse_st' cond x i;
      close_open_inverse_st' body x i

    | Tm_If t0 t1 t2 post ->
      close_open_inverse' t0 x i;    
      close_open_inverse_st' t1 x i;    
      close_open_inverse_st' t2 x i;
      close_open_inverse_opt' post x (i + 1)

    | Tm_Par preL eL postL preR eR postR ->
      close_open_inverse' preL x i;
      close_open_inverse_st' eL x i;
      close_open_inverse' postL x (i + 1);
      close_open_inverse' preR x i;
      close_open_inverse_st' eR x i;
      close_open_inverse' postR x (i + 1)

    | Tm_WithLocal t1 t2 ->
      close_open_inverse' t1 x i;
      close_open_inverse_st' t2 x (i + 1)

    | Tm_Rewrite	t1 t2 ->
						close_open_inverse' t1 x i;
						close_open_inverse' t2 x i

    | Tm_Admit _ _ t post ->
      close_open_inverse' t x i;
      close_open_inverse_opt' post x (i + 1)

    | Tm_Protect t ->
      close_open_inverse_st' t x i
      
let close_open_inverse (t:term) (x:var { ~(x `Set.mem` freevars t) } )
  : Lemma (ensures close_term (open_term t x) x == t)
  = close_open_inverse' t x 0

let close_open_inverse_st (t:st_term) (x:var { ~(x `Set.mem` freevars_st t) } )
  : Lemma (ensures close_st_term (open_st_term t x) x == t)
  = close_open_inverse_st' t x 0

let open_with_gt_ln (e:term) (i:nat) (t:term) (j:nat)
  : Lemma
      (requires ln' e i /\ i < j)
      (ensures open_term' e t j == e) =
  admit ()

let close_with_non_freevar (e:term) (x:var) (i:nat)
  : Lemma
      (requires ~ (x `Set.mem` freevars e))
      (ensures close_term' e x i == e) =
  admit ()

let close_comp_with_non_free_var (c:comp) (x:var) (i:nat)
  : Lemma
    (requires ~ (x `Set.mem` freevars_comp c))
    (ensures close_comp' c x i == c) =
  admit ()
