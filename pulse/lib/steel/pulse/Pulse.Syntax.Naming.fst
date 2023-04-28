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
  = match t with
    | Tm_Return _ _ t ->
      freevars t
    | Tm_Abs b _ pre_hint body post_hint ->
      Set.union (freevars b.binder_ty) 
                (Set.union (freevars_st body)
                           (Set.union (freevars_opt pre_hint)
                                      (freevars_opt post_hint)))
    | Tm_STApp t1 _ t2 ->
      Set.union (freevars t1) (freevars t2)
    | Tm_Bind t1 t2 ->
      Set.union (freevars_st t1) (freevars_st t2)
    | Tm_If t e1 e2 post ->
      Set.union (Set.union (freevars t) (freevars_st e1))
                (Set.union (freevars_st e2) (freevars_opt post))
    | Tm_ElimExists p ->
      freevars p
    | Tm_IntroExists _ e p ->
      Set.union (freevars e) (freevars_list p)
    | Tm_While inv cond body ->
      Set.union (freevars inv)
                (Set.union (freevars_st cond) (freevars_st body))
    | Tm_Par preL eL postL preR eR postR ->
      Set.union
        (Set.union (freevars preL)
                   (Set.union (freevars_st eL)
                              (freevars postL)))
        (Set.union (freevars preR)
                   (Set.union (freevars_st eR)
                              (freevars postR)))

    | Tm_WithLocal t1 t2 ->
      Set.union (freevars t1) (freevars_st t2)

    | Tm_Rewrite t1 t2 ->
						Set.union (freevars t1) (freevars t2)

    | Tm_Admit _ _ t post ->
      Set.union (freevars t) (freevars_opt post)
    | Tm_Protect t -> freevars_st t

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
  = match t with
    | Tm_Return _ _ t ->
      ln' t i
      
    | Tm_Abs b _ pre_hint body post ->
      ln' b.binder_ty i &&
      ln_st' body (i + 1) &&
      ln_opt' pre_hint (i + 1) &&
      ln_opt' post (i + 2)
  
    | Tm_STApp t1 _ t2 ->
      ln' t1 i &&
      ln' t2 i

    | Tm_Bind t1 t2 ->
      ln_st' t1 i &&
      ln_st' t2 (i + 1)

    | Tm_If b then_ else_ post ->
      ln' b i &&
      ln_st' then_ i &&
      ln_st' else_ i &&
      ln_opt' post (i + 1)
  
    | Tm_ElimExists p -> ln' p i
    | Tm_IntroExists _ p e -> ln' p i && ln_list' e i
  
    | Tm_While inv cond body ->
      ln' inv (i + 1) &&
      ln_st' cond i &&
      ln_st' body i

    | Tm_Par preL eL postL preR eR postR ->
      ln' preL i &&
      ln_st' eL i &&
      ln' postL (i + 1) &&
      ln' preR i &&
      ln_st' eR i &&
      ln' postR (i + 1)

    | Tm_WithLocal t1 t2 ->
      ln' t1 i &&
      ln_st' t2 (i + 1)

    | Tm_Rewrite t1 t2 ->
						ln' t1 i &&
						ln' t2 i

    | Tm_Admit _ _ t post ->
      ln' t i &&
      ln_opt' post (i + 1)

    | Tm_Protect t ->
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

let rec open_st_term' (t:st_term) (v:term) (i:index)
  : Tot st_term (decreases t)
  = match t with
    | Tm_Return c use_eq t ->
      Tm_Return c use_eq (open_term' t v i)

    | Tm_Abs b q pre_hint body post ->
      Tm_Abs {b with binder_ty=open_term' b.binder_ty v i} q
             (open_term_opt' pre_hint v (i + 1))
             (open_st_term' body v (i + 1))
             (open_term_opt' post v (i + 2))

    | Tm_STApp head q arg ->
      Tm_STApp (open_term' head v i) q
               (open_term' arg v i)

    | Tm_Bind e1 e2 ->
      Tm_Bind (open_st_term' e1 v i)
              (open_st_term' e2 v (i + 1))

    | Tm_If b then_ else_ post ->
      Tm_If (open_term' b v i)
            (open_st_term' then_ v i)
            (open_st_term' else_ v i)
            (open_term_opt' post v (i + 1))

    | Tm_ElimExists p ->
      Tm_ElimExists (open_term' p v i)
      
    | Tm_IntroExists b p e ->
      Tm_IntroExists b (open_term' p v i)
                       (open_term_list' e v i)
                             

    | Tm_While inv cond body ->
      Tm_While (open_term' inv v (i + 1))
               (open_st_term' cond v i)
               (open_st_term' body v i)

    | Tm_Par preL eL postL preR eR postR ->
      Tm_Par (open_term' preL v i)
             (open_st_term' eL v i)
             (open_term' postL v (i + 1))
             (open_term' preR v i)
             (open_st_term' eR v i)
             (open_term' postR v (i + 1))

    | Tm_WithLocal e1 e2 ->
      Tm_WithLocal (open_term' e1 v i)
                   (open_st_term' e2 v (i + 1))

    | Tm_Rewrite	e1 e2 ->
						Tm_Rewrite (open_term' e1 v i)
																	(open_term' e2 v i)

    | Tm_Admit c u t post ->
      Tm_Admit c u (open_term' t v i)
                   (open_term_opt' post v (i + 1))

    | Tm_Protect t ->
      Tm_Protect (open_st_term' t v i)

let open_term t v =
    open_term' t (Tm_Var { nm_ppname=RT.pp_name_default;
                           nm_index=v;
                           nm_range=FStar.Range.range_0}) 0

let open_st_term t v =
    open_st_term' t (Tm_Var { nm_ppname=RT.pp_name_default;
                              nm_index=v;
                              nm_range=FStar.Range.range_0}) 0

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


let rec close_st_term' (t:st_term) (v:var) (i:index)
  : Tot st_term (decreases t)
  = match t with
    | Tm_Return c use_eq t ->
      Tm_Return c use_eq (close_term' t v i)

    | Tm_Abs b q pre_hint body post ->
      Tm_Abs {b with binder_ty=close_term' b.binder_ty v i} q
             (close_term_opt' pre_hint v (i + 1))
             (close_st_term' body v (i + 1))
             (close_term_opt' post v (i + 2))

    | Tm_STApp head q arg ->
      Tm_STApp (close_term' head v i) q
               (close_term' arg v i)

    | Tm_Bind e1 e2 ->
      Tm_Bind (close_st_term' e1 v i)
              (close_st_term' e2 v (i + 1))

    | Tm_If b then_ else_ post ->
      Tm_If (close_term' b v i)
            (close_st_term' then_ v i)
            (close_st_term' else_ v i)
            (close_term_opt' post v (i + 1))

    | Tm_ElimExists p ->
      Tm_ElimExists (close_term' p v i)
      
    | Tm_IntroExists b p e ->
      Tm_IntroExists b (close_term' p v i)
                       (close_term_list' e v i)

    | Tm_While inv cond body ->
      Tm_While (close_term' inv v (i + 1))
               (close_st_term' cond v i)
               (close_st_term' body v i)

    | Tm_Par preL eL postL preR eR postR ->
      Tm_Par (close_term' preL v i)
             (close_st_term' eL v i)
             (close_term' postL v (i + 1))
             (close_term' preR v i)
             (close_st_term' eR v i)
             (close_term' postR v (i + 1))

    | Tm_WithLocal e1 e2 ->
      Tm_WithLocal (close_term' e1 v i)
                   (close_st_term' e2 v (i + 1))

    | Tm_Rewrite	e1 e2 ->
						Tm_Rewrite (close_term' e1 v i)
																	(close_term' e2 v i)

    | Tm_Admit c u t post ->
      Tm_Admit c u (close_term' t v i)
                   (close_term_opt' post v (i + 1))

    | Tm_Protect t ->
      Tm_Protect (close_st_term' t v i)
      
let close_term t v = close_term' t v 0
let close_st_term t v = close_st_term' t v 0
let close_comp t v = close_comp' t v 0

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

    | Tm_FStar t ->
      RT.close_open_inverse' i t x

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
          (decreases t)
  = close_open_inverse' t x 0

let close_open_inverse_st (t:st_term) (x:var { ~(x `Set.mem` freevars_st t) } )
  : Lemma (ensures close_st_term (open_st_term t x) x == t)
          (decreases t)
  = close_open_inverse_st' t x 0
