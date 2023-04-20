module Pulse.Syntax
module RTB = FStar.Reflection.Typing.Builtins
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
open FStar.List.Tot
module T = FStar.Tactics

type constant =
  | Unit
  | Bool of bool
  | Int of int

let var = nat
let index = nat

type universe = 
  | U_zero
  | U_succ of universe
  | U_var of string
  | U_max : universe -> universe -> universe
  | U_unknown

(* locally nameless.
   term is currently an eqtype. That makes some experiments a bit easier.
   but it doesn't have to be. 
   
   if we include Embed it won't be.
   So, we should remove reliance on this thing being an eqtype soon.
   But, adding a Tm_Embed poses some other difficulties too, 
   
     e.g., opening/closing a term with embedded terms in it becomes
           problematic since that makes opening/closing mutually
           recursive with elaboration
*)

let ppname = RT.pp_name_t
let range = FStar.Sealed.Inhabited.sealed #Prims.range RTB.dummy_range
let default_range : range = FStar.Sealed.seal (Prims.mk_range "" 0 0 0 0)
let range_of_term (t:FStar.Reflection.term) : range = FStar.Sealed.seal (FStar.Reflection.range_of_term t)

noeq
type bv = {
  bv_index  : index;
  bv_ppname : ppname;
  bv_range  : range;
}

noeq
type nm = {
  nm_index  : var;
  nm_ppname : ppname;
  nm_range  : range;
}

type qualifier =
  | Implicit

let should_elim_t = FStar.Sealed.Inhabited.sealed false
let should_elim_true : should_elim_t = FStar.Sealed.Inhabited.seal true
let should_elim_false : should_elim_t = FStar.Sealed.Inhabited.seal false

noeq
type fv = {
  fv_name : R.name;
  fv_range : range;
}
let as_fv l = { fv_name = l; fv_range = default_range }


[@@ no_auto_projectors]
noeq
type term =
  | Tm_BVar       : bv -> term
  | Tm_Var        : nm -> term
  | Tm_FVar       : l:fv -> term
  | Tm_UInst      : l:fv -> us:list universe -> term
  | Tm_Constant   : c:constant -> term
  | Tm_Refine     : b:binder -> term -> term
  | Tm_PureApp    : head:term -> arg_qual:option qualifier -> arg:term -> term
  | Tm_Let        : t:term -> e1:term -> e2:term -> term  
  | Tm_Emp        : term
  | Tm_Pure       : p:term -> term
  | Tm_Star       : l:vprop -> r:vprop -> term
  | Tm_ExistsSL   : u:universe -> t:term -> body:vprop -> should_elim:should_elim_t -> term
  | Tm_ForallSL   : u:universe -> t:term -> body:vprop -> term
  | Tm_Arrow      : b:binder -> q:option qualifier -> body:comp -> term 
  | Tm_Type       : universe -> term
  | Tm_VProp      : term
  | Tm_Inames     : term  // type inames
  | Tm_EmpInames  : term
  | Tm_UVar       : int -> term
  | Tm_Unknown    : term


and binder = {
  binder_ty     : term;
  binder_ppname : ppname;
}

and comp =
  | C_Tot      : term -> comp
  | C_ST       : st_comp -> comp
  | C_STAtomic : term -> st_comp -> comp  // inames
  | C_STGhost  : term -> st_comp -> comp  // inames

and st_comp = { (* ST pre (x:res) post ... x is free in post *)
  u:universe;
  res:term;
  pre:vprop;
  post:vprop
}

and vprop = term

let comp_st = c:comp {not (C_Tot? c) }

type ctag =
  | STT
  | STT_Atomic
  | STT_Ghost

(* terms with STT types *)
[@@ no_auto_projectors]
noeq
type st_term =
  | Tm_Return     : ctag -> bool -> term -> st_term  // bool is whether insert equality in the post
  | Tm_Abs        : b:binder -> q:option qualifier -> pre:option vprop -> body:st_term -> post:option vprop -> st_term
  | Tm_STApp      : head:term -> arg_qual:option qualifier -> arg:term -> st_term  
  | Tm_Bind       : e1:st_term -> e2:st_term -> st_term
  | Tm_If         : b:term -> then_:st_term -> else_:st_term -> post:option vprop -> st_term
  | Tm_ElimExists : vprop -> st_term
  | Tm_IntroExists: erased:bool -> vprop -> witnesses:list term -> st_term
  | Tm_While      : term -> st_term -> st_term -> st_term  // inv, cond, body
  | Tm_Par        : term -> st_term -> term -> term -> st_term -> term -> st_term  // (pre, e, post) for left and right computations

  | Tm_Rewrite    : term -> term -> st_term
  | Tm_Admit      : ctag -> universe -> term -> option term -> st_term  // u, a:type_u, optional post
  | Tm_Protect    : st_term -> st_term //Wrap a term to indicate that no proof-automation heuristics should be applied 

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

    | Tm_Rewrite t1 t2 ->
						Set.union (freevars t1) (freevars t2)

    | Tm_Admit _ _ t post ->
      Set.union (freevars t) (freevars_opt post)
    | Tm_Protect t -> freevars_st t

let rec ln' (t:term) (i:int) =
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
    
and ln_c' (c:comp) (i:int)
  : Tot bool
  = match c with
    | C_Tot t -> ln' t i
    | C_ST s -> ln_st_comp s i
    | C_STAtomic inames s
    | C_STGhost inames s ->
      ln' inames i &&
      ln_st_comp s i

and ln_st_comp (s:st_comp) (i:int) : bool =
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
  : Tot bool
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
                           nm_range=default_range}) 0

let open_st_term t v =
    open_st_term' t (Tm_Var { nm_ppname=RT.pp_name_default;
                              nm_index=v;
                              nm_range=default_range}) 0

let open_comp_with (c:comp) (x:term) = open_comp' c x 0

let rec close_term' (t:term) (v:var) (i:index)
  : term
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

let comp_res (c:comp) : term =
  match c with
  | C_Tot ty -> ty
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s.res

let stateful_comp (c:comp) =
  C_ST? c || C_STAtomic? c || C_STGhost? c

let st_comp_of_comp (c:comp{stateful_comp c}) : st_comp =
  match c with
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s

let with_st_comp (c:comp{stateful_comp c}) (s:st_comp) : comp =
  match c with
  | C_ST _ -> C_ST s
  | C_STAtomic inames _ -> C_STAtomic inames s
  | C_STGhost inames _ -> C_STGhost inames s

let comp_u (c:comp { stateful_comp c }) =
  match c with
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s.u

let comp_pre (c:comp { stateful_comp c }) =
  match c with
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s.pre

let comp_post (c:comp { stateful_comp c }) =
  match c with
  | C_ST s
  | C_STAtomic _ s
  | C_STGhost _ s -> s.post

let comp_inames (c:comp { C_STAtomic? c \/ C_STGhost? c }) : term =
  match c with
  | C_STAtomic inames _
  | C_STGhost inames _ -> inames

let term_of_var (x:var) = Tm_Var { nm_ppname=RT.pp_name_default; nm_index=x; nm_range=default_range}

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

let null_binder (t:term) : binder =
  {binder_ty=t;binder_ppname=RT.pp_name_default}

let mk_binder (s:string) (t:term) : binder =
  {binder_ty=t;binder_ppname=RT.seal_pp_name s}

let mk_bvar (s:string) (r:range) (i:index) : term =
  Tm_BVar {bv_index=i;bv_ppname=RT.seal_pp_name s;bv_range=r}

let null_var (v:var) : term = Tm_Var {nm_index=v;nm_ppname=RT.pp_name_default;nm_range=default_range}

let null_bvar (i:index) : term = Tm_BVar {bv_index=i;bv_ppname=RT.pp_name_default;bv_range=default_range}

let gen_uvar (t:term) : T.Tac term =
  Tm_UVar (T.fresh ())

let rec eq_tm (t1 t2:term) 
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | Tm_VProp, Tm_VProp
    | Tm_Emp, Tm_Emp
    | Tm_Inames, Tm_Inames
    | Tm_EmpInames, Tm_EmpInames
    | Tm_Unknown, Tm_Unknown -> true
    | Tm_BVar x1, Tm_BVar x2 -> x1.bv_index = x2.bv_index
    | Tm_Var x1,  Tm_Var x2 -> x1.nm_index = x2.nm_index
    | Tm_FVar x1, Tm_FVar x2 -> x1.fv_name = x2.fv_name
    | Tm_UInst x1 us1, Tm_UInst x2 us2 -> x1.fv_name=x2.fv_name && us1=us2
    | Tm_Constant c1, Tm_Constant c2 -> c1=c2
    | Tm_Refine b1 t1, Tm_Refine b2 t2 -> 
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_tm t1 t2
    | Tm_PureApp h1 o1 t1, Tm_PureApp h2 o2 t2 ->
      eq_tm h1 h2 &&
      o1=o2 &&
      eq_tm t1 t2
    | Tm_Star l1 r1, Tm_Star l2 r2 ->
      eq_tm l1 l2 &&
      eq_tm r1 r2
    | Tm_Pure p1, Tm_Pure p2 ->
      eq_tm p1 p2
    | Tm_Type u1, Tm_Type u2 ->
      u1=u2
    | Tm_Let t1 e1 e1', Tm_Let t2 e2 e2' ->
      eq_tm t1 t2 &&
      eq_tm e1 e2 &&
      eq_tm e1' e2'
    | Tm_ExistsSL u1 t1 b1 _, Tm_ExistsSL u2 t2 b2 _
    | Tm_ForallSL u1 t1 b1, Tm_ForallSL u2 t2 b2 ->
      u1=u2 &&
      eq_tm t1 t2 &&
      eq_tm b1 b2
    | Tm_Arrow b1 q1 c1, Tm_Arrow b2 q2 c2 ->
      eq_tm b1.binder_ty b2.binder_ty &&
      q1=q2 &&
      eq_comp c1 c2
    | Tm_UVar z1, Tm_UVar z2 ->
      z1=z2
    | _ -> false
    
and eq_comp (c1 c2:comp) 
  : b:bool { b <==> (c1 == c2) }
  = match c1, c2 with
    | C_Tot t1, C_Tot t2 ->
      eq_tm t1 t2
    | C_ST s1, C_ST s2 ->
      eq_st_comp s1 s2
    | C_STAtomic i1 s1, C_STAtomic i2 s2
    | C_STGhost i1 s1, C_STGhost i2 s2 ->
      eq_tm i1 i2 &&
      eq_st_comp s1 s2
    | _ -> false

and eq_st_comp (s1 s2:st_comp)  
  : b:bool { b <==> (s1 == s2) }
  = s1.u=s2.u && 
    eq_tm s1.res s2.res &&
    eq_tm s1.pre s2.pre &&
    eq_tm s1.post s2.post

let eq_tm_opt (t1 t2:option term)
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | None, None -> true
    | Some t1, Some t2 -> eq_tm t1 t2
    | _ -> false

let rec eq_tm_list (t1 t2:list term)
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | [], [] -> true
    | h1::t1, h2::t2 ->
      eq_tm h1 h2 &&
      eq_tm_list t1 t2
    | _ -> false

let rec eq_st_term (t1 t2:st_term) 
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | Tm_Return c1 use_eq1 t1, Tm_Return c2 use_eq2 t2 ->
      c1 = c2 &&
      use_eq1 = use_eq2 &&
      eq_tm t1 t2
      
    | Tm_Abs b1 o1 p1 t1 q1, Tm_Abs b2 o2 p2 t2 q2 ->
      eq_tm b1.binder_ty b2.binder_ty &&
      o1=o2 &&
      eq_tm_opt p1 p2 &&
      eq_st_term t1 t2 &&
      eq_tm_opt q1 q2
  
    | Tm_STApp h1 o1 t1, Tm_STApp h2 o2 t2 ->
      eq_tm h1 h2 &&
      o1=o2 &&
      eq_tm t1 t2

    | Tm_Bind t1 k1, Tm_Bind t2 k2 ->
      eq_st_term t1 t2 &&
      eq_st_term k1 k2
      
    | Tm_IntroExists b1 p1 l1, Tm_IntroExists b2 p2 l2 ->
      b1 = b2 &&
      eq_tm p1 p2 &&
      eq_tm_list l1 l2

    | Tm_ElimExists p1, Tm_ElimExists p2 ->
      eq_tm p1 p2

    | Tm_If g1 ethen1 eelse1 p1, Tm_If g2 ethen2 eelse2 p2 ->
      eq_tm g1 g2 &&
      eq_st_term ethen1 ethen2 &&
      eq_st_term eelse1 eelse2 &&
      eq_tm_opt p1 p2
    
    | Tm_While inv1 cond1 body1, Tm_While inv2 cond2 body2 ->
      eq_tm inv1 inv2 &&
      eq_st_term cond1 cond2 &&
      eq_st_term body1 body2

    | Tm_Par preL1 eL1 postL1 preR1 eR1 postR1,
      Tm_Par preL2 eL2 postL2 preR2 eR2 postR2 ->      
      eq_tm preL1 preL2 &&
      eq_st_term eL1 eL2 &&
      eq_tm postL1 postL2 &&
      eq_tm preR1 preR2 &&
      eq_st_term eR1 eR2 &&
      eq_tm postR1 postR2

    | Tm_Rewrite	e1 e2, Tm_Rewrite e3 e4 ->
						eq_tm e1 e3 &&
						eq_tm e2 e4

    | Tm_Admit c1 u1 t1 post1, Tm_Admit c2 u2 t2 post2 ->
      c1 = c2 &&
      u1 = u2 &&
      eq_tm t1 t2 &&
      eq_tm_opt post1 post2

    | Tm_Protect t1, Tm_Protect t2 ->
      eq_st_term t1 t2
      
    | _ -> false

let rec leftmost_head_and_args (t:term) : term & list (option qualifier & term) =
  match t with
  | Tm_PureApp hd q arg ->
    let hd, args = leftmost_head_and_args hd in
    hd, args@[q, arg]
  | _ -> t, []
