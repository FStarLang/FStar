module Pulse.Syntax.Naming

open FStar.List.Tot
open Pulse.Syntax.Base

module L = FStar.List.Tot

module R = FStar.Reflection
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing

module U = Pulse.Syntax.Pure
module E = Pulse.Elaborate.Pure

let rec freevars (t:term) 
  : Set.set var
  = match t with
    | Tm_Emp
    | Tm_VProp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown -> Set.empty
    | Tm_Star t1 t2 ->
      Set.union (freevars t1) (freevars t2)
    | Tm_ExistsSL _ t1 t2
    | Tm_ForallSL _ t1 t2 ->
      Set.union (freevars t1.binder_ty) (freevars t2)
    | Tm_Pure p -> freevars p
    | Tm_FStar t _ -> RT.freevars t

let freevars_st_comp (s:st_comp) : Set.set var =
  freevars s.res `Set.union`
  freevars s.pre `Set.union`
  freevars s.post


let freevars_comp (c:comp) : Tot (Set.set var) (decreases c) =
  match c with
  | C_Tot t -> freevars t
  | C_ST s -> freevars_st_comp s
  | C_STAtomic inames s
  | C_STGhost inames s ->
    freevars inames `Set.union` freevars_st_comp s

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
    | Tm_Abs { b; pre; body; ret_ty; post } ->
      Set.union (freevars b.binder_ty) 
                (Set.union (freevars_st body)
                           (Set.union (freevars_opt pre)
                                      (Set.union (freevars_opt ret_ty)
                                                 (freevars_opt post))))
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

    | Tm_IntroPure { p }
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

    | Tm_WithLocal { binder; initializer; body } ->
      Set.union (freevars binder.binder_ty)
                (Set.union (freevars initializer)
                           (freevars_st body))

    | Tm_Rewrite { t1; t2 } ->
      Set.union (freevars t1) (freevars t2)

    | Tm_Admit { typ; post } ->
      Set.union (freevars typ)
                (freevars_opt post)

    | Tm_Protect { t } -> freevars_st t

let rec ln' (t:term) (i:int) : Tot bool (decreases t) =
  match t with
  | Tm_Emp
  | Tm_VProp
  | Tm_Inames
  | Tm_EmpInames
  | Tm_Unknown -> true

  | Tm_Star t1 t2 ->
    ln' t1 i &&
    ln' t2 i

  | Tm_Pure p ->
    ln' p i

  | Tm_ExistsSL _ t body
  | Tm_ForallSL _ t body ->
    ln' t.binder_ty i &&
    ln' body (i + 1)
    
  | Tm_FStar t _ ->
    RT.ln' t i

let ln_st_comp (s:st_comp) (i:int) : bool =
  ln' s.res i &&
  ln' s.pre i &&
  ln' s.post (i + 1) (* post has 1 impliict abstraction *)


let ln_c' (c:comp) (i:int)
  : bool
  = match c with
    | C_Tot t -> ln' t i
    | C_ST s -> ln_st_comp s i
    | C_STAtomic inames s
    | C_STGhost inames s ->
      ln' inames i &&
      ln_st_comp s i

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
      
    | Tm_Abs { b; pre; body; ret_ty; post } ->
      ln' b.binder_ty i &&
      ln_st' body (i + 1) &&
      ln_opt' pre (i + 1) &&
      ln_opt' ret_ty (i + 1) &&
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
  
    | Tm_IntroPure { p }
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

    | Tm_WithLocal { binder; initializer; body } ->
      ln' binder.binder_ty i &&
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

noeq
type subst_elt =
  | DT : nat -> term -> subst_elt
  | NT : var -> term -> subst_elt
  | ND : var -> nat -> subst_elt

let shift_subst_elt (n:nat) = function
  | DT i t -> DT (i + n) t
  | NT x t -> NT x t
  | ND x i -> ND x (i + n)

let subst = list subst_elt

let shift_subst_n (n:nat) = L.map (shift_subst_elt n)

let shift_subst = shift_subst_n 1

let rt_subst_elt = function
  | DT i t -> RT.DT i (E.elab_term t)
  | NT x t -> RT.NT x (E.elab_term t)
  | ND x i -> RT.ND x i

let rt_subst = L.map rt_subst_elt

let open_or_close_host_term (t:host_term) (ss:subst)
  : Lemma (not_tv_unknown (RT.subst_term t (rt_subst ss)))
  = admit()

let rec subst_term (t:term) (ss:subst)
  : Tot term (decreases t)
  = match t with
    | Tm_VProp
    | Tm_Emp
    | Tm_Inames
    | Tm_EmpInames
    | Tm_Unknown -> t
                 
    | Tm_Pure p ->
      Tm_Pure (subst_term p ss)
      
    | Tm_Star l r ->
      Tm_Star (subst_term l ss)
              (subst_term r ss)
              
    | Tm_ExistsSL u b body ->
      Tm_ExistsSL u { b with binder_ty = subst_term b.binder_ty ss }
                    (subst_term body (shift_subst ss))
                  
    | Tm_ForallSL u b body ->
      Tm_ForallSL u { b with binder_ty = subst_term b.binder_ty ss }
                    (subst_term body (shift_subst ss))
    
    | Tm_FStar t r ->
      open_or_close_host_term t ss;
      Tm_FStar (RT.subst_term t (rt_subst ss)) r

let open_term' (t:term) (v:term) (i:index) =
  subst_term t [ DT i v ]

let subst_st_comp (s:st_comp) (ss:subst)
 : st_comp =

 { s with res = subst_term s.res ss;
          pre = subst_term s.pre ss;
          post = subst_term s.post (shift_subst ss) }

let open_st_comp' (s:st_comp) (v:term) (i:index) : st_comp =
  subst_st_comp s [ DT i v ]

let subst_comp (c:comp) (ss:subst)
  : comp
  = match c with
    | C_Tot t ->
      C_Tot (subst_term t ss)

    | C_ST s -> C_ST (subst_st_comp s ss)

    | C_STAtomic inames s ->
      C_STAtomic (subst_term inames ss)
                 (subst_st_comp s ss)

    | C_STGhost inames s ->
      C_STGhost (subst_term inames ss)
                (subst_st_comp s ss)

let open_comp' (c:comp) (v:term) (i:index) : comp =
  subst_comp c [ DT i v ]

let subst_term_opt (t:option term) (ss:subst)
  : Tot (option term)
  = match t with
    | None -> None
    | Some t -> Some (subst_term t ss)

let open_term_opt' (t:option term) (v:term) (i:index)
  : Tot (option term) = subst_term_opt t [ DT i v ]

let rec subst_term_list (t:list term) (ss:subst)
  : Tot (list term)
  = match t with
    | [] -> []
    | hd::tl -> subst_term hd ss :: subst_term_list tl ss

let open_term_list' (t:list term) (v:term) (i:index)
  : Tot (list term) = subst_term_list t [ DT i v ]

let subst_binder b ss = 
  {b with binder_ty=subst_term b.binder_ty ss}

let open_binder b v i = 
  {b with binder_ty=open_term' b.binder_ty v i}

let rec subst_st_term (t:st_term) (ss:subst)
  : Tot st_term (decreases t)
  = let t' =
    match t.term with
    | Tm_Return { ctag; insert_eq; term } ->
      Tm_Return { ctag; insert_eq; term=subst_term term ss }

    | Tm_Abs { b; q; pre; body; ret_ty; post } ->
      Tm_Abs { b=subst_binder b ss;
               q;
               pre=subst_term_opt pre (shift_subst ss);
               body=subst_st_term body (shift_subst ss);
               ret_ty=subst_term_opt ret_ty (shift_subst ss);               
               post=subst_term_opt post (shift_subst_n 2 ss) }

    | Tm_STApp { head; arg_qual; arg } ->
      Tm_STApp { head = subst_term head ss;
                 arg_qual;
                 arg=subst_term arg ss }

    | Tm_Bind { binder; head; body } ->
      Tm_Bind { binder = subst_binder binder ss;
                head = subst_st_term head ss;
                body = subst_st_term body (shift_subst ss) }

    | Tm_TotBind { head; body } ->
      Tm_TotBind { head = subst_term head ss; 
                   body = subst_st_term body (shift_subst ss) }

    | Tm_If { b; then_; else_; post } ->
      Tm_If { b = subst_term b ss;
              then_ = subst_st_term then_ ss;
              else_ = subst_st_term else_ ss;
              post = subst_term_opt post (shift_subst ss) }

    | Tm_IntroPure { p; should_check } ->
      Tm_IntroPure { p = subst_term p ss; should_check }

    | Tm_ElimExists { p } ->
      Tm_ElimExists { p = subst_term p ss }
      
    | Tm_IntroExists { erased; p; witnesses; should_check } ->
      Tm_IntroExists { erased; 
                       p = subst_term p ss;
                       witnesses = subst_term_list witnesses ss;
                       should_check }                             

    | Tm_While { invariant; condition; body; condition_var } ->
      Tm_While { invariant = subst_term invariant (shift_subst ss);
                 condition = subst_st_term condition ss;
                 body = subst_st_term body ss;
                 condition_var }

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      Tm_Par { pre1=subst_term pre1 ss;
               body1=subst_st_term body1 ss;
               post1=subst_term post1 (shift_subst ss);
               pre2=subst_term pre2 ss;
               body2=subst_st_term body2 ss;
               post2=subst_term post2 (shift_subst ss) }

    | Tm_WithLocal { binder; initializer; body } ->
      Tm_WithLocal { binder = subst_binder binder ss;
                     initializer = subst_term initializer ss;
                     body = subst_st_term body (shift_subst ss) }

    | Tm_Rewrite { t1; t2 } ->
      Tm_Rewrite { t1 = subst_term t1 ss;
                   t2 = subst_term t2 ss }

    | Tm_Admit { ctag; u; typ; post } ->
      Tm_Admit { ctag;
                 u; 
                 typ=subst_term typ ss;
                 post=subst_term_opt post (shift_subst ss) }

    | Tm_Protect { t } ->
      Tm_Protect { t = subst_st_term t ss }
    in
    { t with term = t' }

let open_st_term' (t:st_term) (v:term) (i:index) : st_term =
  subst_st_term t [ DT i v ]

let open_term_nv t nv =
    open_term' t (U.term_of_nvar nv) 0

// Can use this no-name version in specs only
let open_term t v : GTot term =
    open_term_nv t (v_as_nv v)

let open_st_term_nv t nv =
    open_st_term' t (U.term_of_nvar nv) 0

// Can use this no-name version in specs only
let open_st_term t v : GTot st_term =
    open_st_term_nv t (v_as_nv v)

let open_comp_with (c:comp) (x:term) = open_comp' c x 0

let close_term' (t:term) (v:var) (i:index) : term =
  subst_term t [ ND v i ]

let close_st_comp' (s:st_comp) (v:var) (i:index) : st_comp =
  subst_st_comp s [ ND v i ]

let close_comp' (c:comp) (v:var) (i:index) : comp =
  subst_comp c [ ND v i ]

let close_term_opt' (t:option term) (v:var) (i:index) : option term =
  subst_term_opt t [ ND v i ]

let  close_term_list' (t:list term) (v:var) (i:index) : list term =
  subst_term_list t [ ND v i ]

let close_binder b v i =
  subst_binder b [ ND v i ]
             
let close_st_term' (t:st_term) (v:var) (i:index) : st_term =
  subst_st_term t [ ND v i ]
      
let close_term t v = close_term' t v 0
let close_st_term t v = close_st_term' t v 0
let close_comp t v = close_comp' t v 0

val close_open_inverse' (t:term) 
                        (x:var { ~(x `Set.mem` freevars t) } )
                        (i:index)
  : Lemma (ensures close_term' (open_term' t (U.term_of_no_name_var x) i) x i == t)

val close_open_inverse_comp' (c:comp)
                             (x:var { ~(x `Set.mem` freevars_comp c) } )
                             (i:index)
  : Lemma (ensures close_comp' (open_comp' c (U.term_of_no_name_var x) i) x i == c)

val close_open_inverse_opt' (t:option term)
                            (x:var { ~(x `Set.mem` freevars_opt t) })
                            (i:index)
  : Lemma (ensures close_term_opt' (open_term_opt' t (U.term_of_no_name_var x) i) x i == t)

val close_open_inverse_list' (t:list term)
                             (x:var { ~(x `Set.mem` freevars_list t) })
                             (i:index)
  : Lemma (ensures close_term_list' (open_term_list' t (U.term_of_no_name_var x) i) x i == t)

val close_open_inverse_st' (t:st_term) 
                           (x:var { ~(x `Set.mem` freevars_st t) } )
                           (i:index)
  : Lemma (ensures close_st_term' (open_st_term' t (U.term_of_no_name_var x) i) x i == t)

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

val open_with_gt_ln_st (s:st_comp) (i:int) (t:term) (j:nat)
  : Lemma (requires ln_st_comp s i /\ i < j)
          (ensures open_st_comp' s t j == s)

val open_with_gt_ln_comp (c:comp) (i:int) (t:term) (j:nat)
  : Lemma (requires ln_c' c i /\ i < j)
          (ensures open_comp' c t j == c)

val close_with_non_freevar (e:term) (x:var) (i:nat)
  : Lemma
      (requires ~ (x `Set.mem` freevars e))
      (ensures close_term' e x i == e)

val close_with_non_freevar_st (s:st_comp) (x:var) (i:nat)
  : Lemma
    (requires ~ (x `Set.mem` freevars_st_comp s))
    (ensures close_st_comp' s x i == s)

val close_comp_with_non_free_var (c:comp) (x:var) (i:nat)
  : Lemma
    (requires ~ (x `Set.mem` freevars_comp c))
    (ensures close_comp' c x i == c)
