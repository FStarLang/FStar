module Pulse.Syntax
module RT = Refl.Typing
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

type bv = {
  bv_index  : index;
  bv_ppname : string
}

type nm = {
  nm_index  : var;
  nm_ppname : string
}

type qualifier =
  | Implicit

[@@ no_auto_projectors]
type term =
  // | Tm_Embed    : R.term -> term // a host term included as is in Pulse
  | Tm_BVar       : bv -> term
  | Tm_Var        : nm -> term
  | Tm_FVar       : l:R.name -> term
  | Tm_UInst      : l:R.name -> us:list universe -> term
  | Tm_Constant   : c:constant -> term
  | Tm_Refine     : b:binder -> term -> term
  | Tm_Abs        : b:binder -> q:option qualifier -> pre:vprop -> body:term -> post:option vprop -> term
  | Tm_PureApp    : head:term -> arg_qual:option qualifier -> arg:term -> term
  | Tm_Let        : t:term -> e1:term -> e2:term -> term  
  | Tm_STApp      : head:term -> arg_qual:option qualifier -> arg:term -> term  
  | Tm_Bind       : e1:term -> e2:term -> term
  | Tm_Emp        : term
  | Tm_Pure       : p:term -> term
  | Tm_Star       : l:vprop -> r:vprop -> term
  | Tm_ExistsSL   : u:universe -> t:term -> body:vprop -> term
  | Tm_ForallSL   : u:universe -> t:term -> body:vprop -> term
  | Tm_Arrow      : b:binder -> q:option qualifier -> body:comp -> term 
  | Tm_Type       : universe -> term
  | Tm_VProp      : term
  | Tm_If         : term -> term -> term -> post:option vprop -> term

  | Tm_Inames     : term  // type inames
  | Tm_EmpInames  : term

  | Tm_ElimExists : term -> term
  | Tm_IntroExists: term -> term -> term

  | Tm_UVar       : int -> term

and binder = {
  binder_ty     : term;
  binder_ppname : string
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
    | Tm_UVar _ -> Set.empty
    | Tm_Var nm -> Set.singleton nm.nm_index
    | Tm_Refine b body
    | Tm_Abs b _ _ body _ ->
      // Q: Why is this not taking freevars of pre (and post)?
      // A: I would like to mark pre and post as unobservable
      Set.union (freevars b.binder_ty) (freevars body)
    | Tm_PureApp t1 _ t2
    | Tm_STApp t1 _ t2
    | Tm_Star  t1 t2
    | Tm_ExistsSL _ t1 t2
    | Tm_ForallSL _ t1 t2 
    | Tm_Bind t1 t2 -> Set.union (freevars t1) (freevars t2)

    | Tm_Let t e1 e2 ->
      Set.union (Set.union (freevars t) (freevars e1)) (freevars e2)
    | Tm_If t e1 e2 post ->
      Set.union (Set.union (freevars t) (freevars e1))
                (Set.union (freevars e2) (freevars_term_option post))

    | Tm_Pure p -> freevars p

    | Tm_Arrow b _ body -> Set.union (freevars b.binder_ty) (freevars_comp body)
    | Tm_ElimExists p -> freevars p
    | Tm_IntroExists e p -> Set.union (freevars e) (freevars p)

and freevars_comp (c:comp) : Set.set var =
  match c with
  | C_Tot t -> freevars t
  | C_ST s -> freevars_st s
  | C_STAtomic inames s
  | C_STGhost inames s ->
    freevars inames `Set.union` freevars_st s

and freevars_st (s:st_comp) : Set.set var =
  freevars s.res `Set.union`
  freevars s.pre `Set.union`
  freevars s.post

and freevars_term_option (topt:option term) : Set.set var =
  match topt with
  | None -> Set.empty
  | Some t -> freevars t

let rec ln' (t:term) (i:int) =
  match t with
  // | Tm_Embed t -> RT.ln' t i
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
  | Tm_UVar _ -> true

  | Tm_Refine b phi ->
    ln' b.binder_ty i &&
    ln' phi (i + 1)

  | Tm_Abs b _ pre_hint body post ->
    ln' b.binder_ty i &&
    ln' pre_hint (i + 1) &&
    ln' body (i + 1) &&
    (match post with
     | None -> true
     | Some post -> ln' post (i + 2))

  | Tm_STApp t1 _ t2
  | Tm_PureApp t1 _ t2
  | Tm_Star t1 t2 ->
    ln' t1 i &&
    ln' t2 i

  | Tm_Bind t1 t2 ->
    ln' t1 i &&
    ln' t2 (i + 1)

  | Tm_Let t e1 e2 ->
    ln' t i &&
    ln' e1 i &&
    ln' e2 (i + 1)

  | Tm_Pure p ->
    ln' p i

  | Tm_ExistsSL _ t body
  | Tm_ForallSL _ t body ->
    ln' t i &&
    ln' body (i + 1)
    
  | Tm_Arrow b _ c ->
    ln' b.binder_ty i &&
    ln'_comp c (i + 1)
    
  | Tm_If b then_ else_ post ->
    ln' b i &&
    ln' then_ i &&
    ln' else_ i &&
    (match post with
     | None -> true
     | Some post -> ln' post (i+1))

  | Tm_ElimExists p -> ln' p i
  | Tm_IntroExists e p -> ln' e i && ln' p i

and ln'_comp (c:comp) (i:int)
  : Tot bool
  = match c with
    | C_Tot t -> ln' t i
    | C_ST s -> ln'_st_comp s i
    | C_STAtomic inames s
    | C_STGhost inames s ->
      ln' inames i &&
      ln'_st_comp s i

and ln'_st_comp (s:st_comp) (i:int) : bool =
  ln' s.res i &&
  ln' s.pre i &&
  ln' s.post (i + 1) (* post has 1 impliict abstraction *)

let ln (t:term) = ln' t (-1)
let ln_c (c:comp) = ln'_comp c (-1)

let rec open_term' (t:term) (v:term) (i:index)
  : Tot term (decreases t)
  = match t with
    | Tm_BVar bv ->
      if i = bv.bv_index
      then match v with
           | Tm_Var nm ->
             let ppname =
               if nm.nm_ppname = "_" then bv.bv_ppname
               else nm.nm_ppname in
             Tm_Var {nm with nm_ppname=ppname}
           | _ -> v
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
    | Tm_UVar _ -> t

    | Tm_Refine b phi ->
      Tm_Refine {b with binder_ty=open_term' b.binder_ty v i}
                (open_term' phi v (i + 1))

    | Tm_Abs b q pre_hint body post ->
      Tm_Abs {b with binder_ty=open_term' b.binder_ty v i} q
             (open_term' pre_hint v (i + 1))
             (open_term' body v (i + 1))
             (match post with
              | None -> None
              | Some post -> Some (open_term' post v (i + 2)))

    | Tm_PureApp head q arg ->
      Tm_PureApp (open_term' head v i) q
                 (open_term' arg v i)
                 
    | Tm_Let t e1 e2 ->
      Tm_Let (open_term' t v i)
             (open_term' e1 v i)
             (open_term' e2 v (i + 1))
             
    | Tm_STApp head q arg ->
      Tm_STApp (open_term' head v i) q
               (open_term' arg v i)

    | Tm_Bind e1 e2 ->
      Tm_Bind (open_term' e1 v i)
              (open_term' e2 v (i + 1))

    | Tm_Pure p ->
      Tm_Pure (open_term' p v i)
      
    | Tm_Star l r ->
      Tm_Star (open_term' l v i)
              (open_term' r v i)
              
    | Tm_ExistsSL u t body ->
      Tm_ExistsSL u (open_term' t v i)
                    (open_term' body v (i + 1))
                  
    | Tm_ForallSL u t body ->
      Tm_ForallSL u (open_term' t v i)
                    (open_term' body v (i + 1))
    
    | Tm_Arrow b q c ->
      Tm_Arrow {b with binder_ty=open_term' b.binder_ty v i} q
               (open_comp' c v (i + 1))

    | Tm_If b then_ else_ post ->
      Tm_If (open_term' b v i)
            (open_term' then_ v i)
            (open_term' else_ v i)
            (match post with
             | None -> None
             | Some post -> Some (open_term' post v (i + 1)))

    | Tm_ElimExists p -> Tm_ElimExists (open_term' p v i)
    | Tm_IntroExists e p -> Tm_IntroExists (open_term' e v i)
                                           (open_term' p v i)

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

let open_term t v =
  open_term' t (Tm_Var {nm_ppname="_";nm_index=v}) 0
let open_comp_with (c:comp) (x:term) = open_comp' c x 0

let rec close_term' (t:term) (v:var) (i:index)
  : term
  = match t with
    | Tm_Var nm ->
      if nm.nm_index = v
      then Tm_BVar {bv_index=i;bv_ppname=nm.nm_ppname}
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
    | Tm_UVar _ -> t

    | Tm_Refine b phi ->
      Tm_Refine {b with binder_ty=close_term' b.binder_ty v i}
                (close_term' phi v (i + 1))

    | Tm_Abs b q pre_hint body post ->
      Tm_Abs {b with binder_ty=close_term' b.binder_ty v i} q
             (close_term' pre_hint v (i + 1))
             (close_term' body v (i + 1))
             (match post with
              | None -> None
              | Some post -> Some (close_term' post v (i + 2)))

    | Tm_PureApp head q arg ->
      Tm_PureApp (close_term' head v i) q
                 (close_term' arg v i)
                 
    | Tm_Let t e1 e2 ->
      Tm_Let (close_term' t v i)
             (close_term' e1 v i)
             (close_term' e2 v (i + 1))
             
    | Tm_STApp head q arg ->
      Tm_STApp (close_term' head v i) q
               (close_term' arg v i)

    | Tm_Bind e1 e2 ->
      Tm_Bind (close_term' e1 v i)
              (close_term' e2 v (i + 1))

    | Tm_Pure p ->
      Tm_Pure (close_term' p v i)
      
    | Tm_Star l r ->
      Tm_Star (close_term' l v i)
              (close_term' r v i)
              
    | Tm_ExistsSL u t body ->
      Tm_ExistsSL u (close_term' t v i)
                    (close_term' body v (i + 1))
                  
    | Tm_ForallSL u t body ->
      Tm_ForallSL u (close_term' t v i)
                    (close_term' body v (i + 1))
    
    | Tm_Arrow b q c ->
      Tm_Arrow {b with binder_ty=close_term' b.binder_ty v i} q
               (close_comp' c v (i + 1))

    | Tm_If b then_ else_ post ->
      Tm_If (close_term' b v i)
            (close_term' then_ v i)
            (close_term' else_ v i)
            (match post with
             | None -> None
             | Some post -> Some (close_term' post v (i + 1)))

    | Tm_ElimExists p -> Tm_ElimExists (close_term' p v i)
    | Tm_IntroExists e p -> Tm_IntroExists (close_term' e v i)
                                           (close_term' p v i)

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

let close_term t v = close_term' t v 0
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

let term_of_var (x:var) = Tm_Var { nm_ppname="_"; nm_index=x}
let rec close_open_inverse' (t:term) (x:var { ~(x `Set.mem` freevars t) } ) (i:index)
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
    | Tm_UVar _ -> ()
    
    | Tm_Pure p ->
      close_open_inverse' p x i

    | Tm_Refine b t ->
      close_open_inverse' b.binder_ty x i;
      close_open_inverse' t x (i + 1)
    | Tm_Abs b _q pre body post ->
      close_open_inverse' b.binder_ty x i;
      assume (close_term' (open_term' pre (term_of_var x) (i + 1)) x (i + 1) == pre);
      close_open_inverse' body x (i + 1);
      if Some? post
      then assume (close_term' (open_term' (Some?.v post) (term_of_var x) (i + 2)) x (i + 2) == Some?.v post)

    | Tm_PureApp l _ r
    | Tm_STApp l _ r
    | Tm_Star l r ->
      close_open_inverse' l x i;
      close_open_inverse' r x i

    | Tm_Bind e1 e2 ->
      close_open_inverse' e1 x i;
      close_open_inverse' e2 x (i + 1)

    | Tm_Let t e1 e2 ->
      close_open_inverse' t x i;    
      close_open_inverse' e1 x i;
      close_open_inverse' e2 x (i + 1)

    | Tm_ExistsSL _ t b
    | Tm_ForallSL _ t b ->
      close_open_inverse' t x i;    
      close_open_inverse' b x (i + 1)
      
    | Tm_If t0 t1 t2 post ->
      close_open_inverse' t0 x i;    
      close_open_inverse' t1 x i;    
      close_open_inverse' t2 x i;          
      (if Some? post then close_open_inverse' (Some?.v post) x (i + 1))
      
    | Tm_Arrow b _ body ->
      close_open_inverse' b.binder_ty x i;
      close_open_inverse'_comp body x (i + 1)

    | Tm_ElimExists t -> close_open_inverse' t x i
    | Tm_IntroExists t e -> close_open_inverse' t x i; close_open_inverse' e x i
      
and close_open_inverse'_comp (c:comp) (x:var { ~(x `Set.mem` freevars_comp c) } ) (i:index)
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
  
let close_open_inverse (t:term) (x:var { ~(x `Set.mem` freevars t) } )
  : Lemma (ensures close_term (open_term t x) x == t)
          (decreases t)
  = close_open_inverse' t x 0

let null_binder (t:term) : binder =
  {binder_ty=t;binder_ppname="_"}

let mk_binder (s:string) (t:term) : binder =
  {binder_ty=t;binder_ppname=s}

let mk_bvar (s:string) (i:index) : term =
  Tm_BVar {bv_index=i;bv_ppname=s}

let null_var (v:var) : term = Tm_Var {nm_index=v;nm_ppname="_"}

let null_bvar (i:index) : term = Tm_BVar {bv_index=i;bv_ppname="_"}

let gen_uvar (t:term) : T.Tac term =
  Tm_UVar (T.fresh ())

let rec term_no_pp (t:term) : term =
  match t with
  | Tm_BVar bv -> Tm_BVar (bv_no_pp bv)
  | Tm_Var nm -> Tm_Var (nm_no_pp nm)
  | Tm_FVar l -> t
  | Tm_UInst _ _ -> t
  | Tm_Constant _ -> t
  | Tm_Refine b t -> Tm_Refine (binder_no_pp b) (term_no_pp t)
  | Tm_Abs b q pre body postopt ->
    Tm_Abs (binder_no_pp b) q (term_no_pp pre) (term_no_pp body) (term_opt_no_pp postopt)
  | Tm_PureApp head q arg ->
    Tm_PureApp (term_no_pp head) q (term_no_pp arg)
  | Tm_Let t e1 e2 ->
    Tm_Let (term_no_pp t) (term_no_pp e1) (term_no_pp e2)
  | Tm_STApp head q arg ->
    Tm_STApp (term_no_pp head) q (term_no_pp arg)
  | Tm_Bind e1 e2 -> Tm_Bind (term_no_pp e1) (term_no_pp e2)
  | Tm_Emp -> t
  | Tm_Pure p -> Tm_Pure (term_no_pp p)
  | Tm_Star l r -> Tm_Star (term_no_pp l) (term_no_pp r)
  | Tm_ExistsSL u t body -> Tm_ExistsSL u (term_no_pp t) (term_no_pp body)
  | Tm_ForallSL u t body -> Tm_ForallSL u (term_no_pp t) (term_no_pp body)
  | Tm_Arrow b q c ->
    Tm_Arrow (binder_no_pp b) q (comp_no_pp c)
  | Tm_Type _ -> t
  | Tm_VProp -> t
  | Tm_If e1 e2 e3 post ->
    Tm_If (term_no_pp e1) (term_no_pp e2) (term_no_pp e3)
          (term_opt_no_pp post)
  | Tm_Inames
  | Tm_EmpInames -> t
  | Tm_ElimExists p -> Tm_ElimExists (term_no_pp p)
  | Tm_IntroExists e p -> Tm_IntroExists (term_no_pp e) (term_no_pp p)
  | Tm_UVar _ -> t

and binder_no_pp (b:binder) : binder =
  {binder_ty = term_no_pp b.binder_ty;
   binder_ppname = "_"}

and bv_no_pp (b:bv) : bv =
  {b with bv_ppname="_"}

and nm_no_pp (x:nm) : nm =
  {x with nm_ppname="_"}

and term_opt_no_pp (t:option term) : option term =
  match t with
  | None -> None
  | Some t -> Some (term_no_pp t)

and comp_no_pp (c:comp) : comp =
  match c with
  | C_Tot t -> C_Tot (term_no_pp t)
  | C_ST s -> C_ST (st_comp_no_pp s)
  | C_STAtomic inames s ->
    C_STAtomic (term_no_pp inames) (st_comp_no_pp s)
  | C_STGhost inames s ->
    C_STGhost (term_no_pp inames) (st_comp_no_pp s)

and st_comp_no_pp (s:st_comp) : st_comp =
  {u=s.u;
   res=term_no_pp s.res;
   pre=term_no_pp s.pre;
   post=term_no_pp s.post}

let eq_tm (t1 t2:term) : bool =
  term_no_pp t1 = term_no_pp t2

let eq_comp (c1 c2:comp) : bool =
  comp_no_pp c1 = comp_no_pp c2
