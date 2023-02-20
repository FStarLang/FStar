module Pulse.Syntax
module RT = Refl.Typing
module R = FStar.Reflection
module Un = FStar.Sealed
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

let ppname = Un.sealed string

noeq
type bv = {
  bv_index  : index;
  bv_ppname : ppname;
}

noeq
type nm = {
  nm_index  : var;
  nm_ppname : ppname;
}

type qualifier =
  | Implicit

[@@ no_auto_projectors]
noeq
type term =
  // | Tm_Embed    : R.term -> term // a host term included as is in Pulse
  | Tm_BVar       : bv -> term
  | Tm_Var        : nm -> term
  | Tm_FVar       : l:R.name -> term
  | Tm_UInst      : l:R.name -> us:list universe -> term
  | Tm_Constant   : c:constant -> term
  | Tm_Refine     : b:binder -> term -> term
  | Tm_Abs        : b:binder -> q:option qualifier -> pre:option vprop -> body:term -> post:option vprop -> term
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

  | Tm_While      : term -> term -> term -> term  // inv, cond, body

  | Tm_UVar       : int -> term

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
    | Tm_Refine b body ->
      Set.union (freevars b.binder_ty) (freevars body)
    | Tm_Abs b _ pre_hint body post_hint ->
      Set.union (freevars b.binder_ty) 
                (Set.union (freevars body)
                           (Set.union (freevars_opt pre_hint)
                                      (freevars_opt post_hint)))
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
                (Set.union (freevars e2) (freevars_opt post))

    | Tm_Pure p -> freevars p

    | Tm_Arrow b _ body -> Set.union (freevars b.binder_ty) (freevars_comp body)
    | Tm_ElimExists p -> freevars p
    | Tm_IntroExists e p -> Set.union (freevars e) (freevars p)
    | Tm_While inv cond body ->
      Set.union (freevars inv)
                (Set.union (freevars cond) (freevars body))

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

and freevars_opt (t:option term) : Set.set var =
  match t with
  | None -> Set.empty
  | Some t -> freevars t
  
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
  | Tm_UVar _ -> true

  | Tm_Refine b phi ->
    ln' b.binder_ty i &&
    ln' phi (i + 1)

  | Tm_Abs b _ pre_hint body post ->
    ln' b.binder_ty i &&
    ln' body (i + 1) &&
    ln'_opt pre_hint (i + 1) &&
    ln'_opt post (i + 2)

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
    ln'_opt post (i + 1)

  | Tm_ElimExists p -> ln' p i
  | Tm_IntroExists e p -> ln' e i && ln' p i

  | Tm_While inv cond body ->
    ln' inv (i + 1) &&
    ln' cond i &&
    ln' body i

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

and ln'_opt (t:option term) (i:int) : bool =
  match t with
  | None -> true
  | Some t -> ln' t i
  
let ln (t:term) = ln' t (-1)
let ln_c (c:comp) = ln'_comp c (-1)

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
    | Tm_UVar _ -> t

    | Tm_Refine b phi ->
      Tm_Refine {b with binder_ty=open_term' b.binder_ty v i}
                (open_term' phi v (i + 1))

    | Tm_Abs b q pre_hint body post ->
      Tm_Abs {b with binder_ty=open_term' b.binder_ty v i} q
             (open_term_opt' pre_hint v (i + 1))
             (open_term' body v (i + 1))
             (open_term_opt' post v (i + 2))

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
            (open_term_opt' post v (i + 1))

    | Tm_ElimExists p -> Tm_ElimExists (open_term' p v i)
    | Tm_IntroExists e p -> Tm_IntroExists (open_term' e v i)
                                           (open_term' p v i)

    | Tm_While inv cond body ->
      Tm_While (open_term' inv v (i + 1))
               (open_term' cond v i)
               (open_term' body v i)

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

and open_term_opt' (t:option term) (v:term) (i:index)
  : Tot (option term)
  = match t with
    | None -> None
    | Some t -> Some (open_term' t v i)
    
let open_term t v =
  open_term' t (Tm_Var {nm_ppname=Sealed.seal "_";nm_index=v}) 0
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
             (close_term_opt' pre_hint v (i + 1))
             (close_term' body v (i + 1))
             (close_term_opt' post v (i + 2))

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
            (close_term_opt' post v (i + 1))

    | Tm_ElimExists p -> Tm_ElimExists (close_term' p v i)
    | Tm_IntroExists e p -> Tm_IntroExists (close_term' e v i)
                                          (close_term' p v i)

    | Tm_While inv cond body ->
      Tm_While (close_term' inv v (i + 1))
               (close_term' cond v i)
               (close_term' body v i)

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

and close_term_opt' (t:option term) (v:var) (i:index)
  : Tot (option term) (decreases t)
  = match t with
    | None -> None
    | Some t -> Some (close_term' t v i)
    
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

let term_of_var (x:var) = Tm_Var { nm_ppname=Sealed.seal "_"; nm_index=x}

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
    | Tm_UVar _ -> ()
    
    | Tm_Pure p
    | Tm_ElimExists p ->
      close_open_inverse' p x i

    | Tm_Refine b t ->
      close_open_inverse' b.binder_ty x i;
      close_open_inverse' t x (i + 1)
      
    | Tm_Abs b _q pre body post ->
      close_open_inverse' b.binder_ty x i;
      close_open_inverse' body x (i + 1);
      close_open_inverse_opt' pre x (i + 1);
      close_open_inverse_opt' post x (i + 2)
    
    | Tm_PureApp l _ r
    | Tm_STApp l _ r
    | Tm_Star l r
    | Tm_IntroExists l r ->
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
      close_open_inverse_opt' post x (i + 1)
      

    | Tm_Arrow b _ body ->
      close_open_inverse' b.binder_ty x i;
      close_open_inverse'_comp body x (i + 1)

    | Tm_ElimExists t -> close_open_inverse' t x i
    | Tm_IntroExists t e -> close_open_inverse' t x i; close_open_inverse' e x i

    | Tm_While inv cond body ->
      close_open_inverse' inv x (i + 1);
      close_open_inverse' cond x i;
      close_open_inverse' body x i

and close_open_inverse'_comp (c:comp)
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

and close_open_inverse_opt' (t:option term)
                            (x:var { ~(x `Set.mem` freevars_opt t) })
                            (i:index)
  : Lemma (ensures close_term_opt' (open_term_opt' t (term_of_var x) i) x i == t)
          (decreases t)
  = match t with
    | None -> ()
    | Some t -> close_open_inverse' t x i

let close_open_inverse (t:term) (x:var { ~(x `Set.mem` freevars t) } )
  : Lemma (ensures close_term (open_term t x) x == t)
          (decreases t)
  = close_open_inverse' t x 0

let null_binder (t:term) : binder =
    {binder_ty=t;binder_ppname=Sealed.seal "_"}

let mk_binder (s:string) (t:term) : binder =
  {binder_ty=t;binder_ppname=Sealed.seal s}

let mk_bvar (s:string) (i:index) : term =
  Tm_BVar {bv_index=i;bv_ppname=Sealed.seal s}

let null_var (v:var) : term = Tm_Var {nm_index=v;nm_ppname=Sealed.seal "_"}

let null_bvar (i:index) : term = Tm_BVar {bv_index=i;bv_ppname=Sealed.seal "_"}

let gen_uvar (t:term) : T.Tac term =
  Tm_UVar (T.fresh ())

// (* We should no longer need this *)
// let rec term_no_pp (t:term) : term =
//   match t with
//   | Tm_BVar bv -> Tm_BVar (bv_no_pp bv)
//   | Tm_Var nm -> Tm_Var (nm_no_pp nm)
//   | Tm_FVar l -> t
//   | Tm_UInst _ _ -> t
//   | Tm_Constant _ -> t
//   | Tm_Refine b t -> Tm_Refine (binder_no_pp b) (term_no_pp t)
//   | Tm_Abs b q pre body postopt ->
//     Tm_Abs (binder_no_pp b) q (term_no_pp pre) (term_no_pp body) (term_opt_no_pp postopt)
//   | Tm_PureApp head q arg ->
//     Tm_PureApp (term_no_pp head) q (term_no_pp arg)
//   | Tm_Let t e1 e2 ->
//     Tm_Let (term_no_pp t) (term_no_pp e1) (term_no_pp e2)
//   | Tm_STApp head q arg ->
//     Tm_STApp (term_no_pp head) q (term_no_pp arg)
//   | Tm_Bind e1 e2 -> Tm_Bind (term_no_pp e1) (term_no_pp e2)
//   | Tm_Emp -> t
//   | Tm_Pure p -> Tm_Pure (term_no_pp p)
//   | Tm_Star l r -> Tm_Star (term_no_pp l) (term_no_pp r)
//   | Tm_ExistsSL u t body -> Tm_ExistsSL u (term_no_pp t) (term_no_pp body)
//   | Tm_ForallSL u t body -> Tm_ForallSL u (term_no_pp t) (term_no_pp body)
//   | Tm_Arrow b q c ->
//     Tm_Arrow (binder_no_pp b) q (comp_no_pp c)
//   | Tm_Type _ -> t
//   | Tm_VProp -> t
//   | Tm_If e1 e2 e3 post ->
//     Tm_If (term_no_pp e1) (term_no_pp e2) (term_no_pp e3)
//           (term_opt_no_pp post)
//   | Tm_Inames
//   | Tm_EmpInames -> t
//   | Tm_ElimExists p -> Tm_ElimExists (term_no_pp p)
//   | Tm_IntroExists e p -> Tm_IntroExists (term_no_pp e) (term_no_pp p)
//   | Tm_UVar _ -> t

// and binder_no_pp (b:binder) : binder =
//   {binder_ty = term_no_pp b.binder_ty;
//    binder_ppname = Un.return "_"}

// and bv_no_pp (b:bv) : bv =
//   {b with bv_ppname=Un.return "_"}

// and nm_no_pp (x:nm) : nm =
//   {x with nm_ppname=Un.return "_"}

// and term_opt_no_pp (t:option term) : option term =
//   match t with
//   | None -> None
//   | Some t -> Some (term_no_pp t)

// and comp_no_pp (c:comp) : comp =
//   match c with
//   | C_Tot t -> C_Tot (term_no_pp t)
//   | C_ST s -> C_ST (st_comp_no_pp s)
//   | C_STAtomic inames s ->
//     C_STAtomic (term_no_pp inames) (st_comp_no_pp s)
//   | C_STGhost inames s ->
//     C_STGhost (term_no_pp inames) (st_comp_no_pp s)

// and st_comp_no_pp (s:st_comp) : st_comp =
//   {u=s.u;
//    res=term_no_pp s.res;
//    pre=term_no_pp s.pre;
//    post=term_no_pp s.post}

let rec eq_tm (t1 t2:term) 
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | Tm_VProp, Tm_VProp
    | Tm_Emp, Tm_Emp
    | Tm_Inames, Tm_Inames
    | Tm_EmpInames, Tm_EmpInames -> true
    | Tm_BVar x1, Tm_BVar x2 -> x1.bv_index = x2.bv_index
    | Tm_Var x1,  Tm_Var x2 -> x1.nm_index = x2.nm_index
    | Tm_FVar x1, Tm_FVar x2 -> x1 = x2
    | Tm_UInst x1 us1, Tm_UInst x2 us2 -> x1=x2 && us1=us2
    | Tm_Constant c1, Tm_Constant c2 -> c1=c2
    | Tm_Refine b1 t1, Tm_Refine b2 t2 -> 
      eq_tm b1.binder_ty b2.binder_ty &&
      eq_tm t1 t2
    | Tm_Abs b1 o1 p1 t1 q1, Tm_Abs b2 o2 p2 t2 q2 ->
      eq_tm b1.binder_ty b2.binder_ty &&
      o1=o2 &&
      eq_tm_opt p1 p2 &&
      eq_tm t1 t2 &&
      eq_tm_opt q1 q2
    | Tm_PureApp h1 o1 t1, Tm_PureApp h2 o2 t2
    | Tm_STApp h1 o1 t1, Tm_STApp h2 o2 t2 ->
      eq_tm h1 h2 &&
      o1=o2 &&
      eq_tm t1 t2
    | Tm_Star l1 r1, Tm_Star l2 r2
    | Tm_Bind l1 r1, Tm_Bind l2 r2
    | Tm_IntroExists l1 r1, Tm_IntroExists l2 r2 ->
      eq_tm l1 l2 &&
      eq_tm r1 r2
    | Tm_ElimExists p1, Tm_ElimExists p2
    | Tm_Pure p1, Tm_Pure p2 ->
      eq_tm p1 p2
    | Tm_Type u1, Tm_Type u2 ->
      u1=u2
    | Tm_Let t1 e1 e1', Tm_Let t2 e2 e2' ->
      eq_tm t1 t2 &&
      eq_tm e1 e2 &&
      eq_tm e1' e2'
    | Tm_If g1 ethen1 eelse1 p1, Tm_If g2 ethen2 eelse2 p2 ->
      eq_tm g1 g2 &&
      eq_tm ethen1 ethen2 &&
      eq_tm eelse1 eelse2 &&
      eq_tm_opt p1 p2
    | Tm_ExistsSL u1 t1 b1, Tm_ExistsSL u2 t2 b2
    | Tm_ForallSL u1 t1 b1, Tm_ForallSL u2 t2 b2 ->
      u1=u2 &&
      eq_tm t1 t2 &&
      eq_tm b1 b2
    | Tm_Arrow b1 q1 c1, Tm_Arrow b2 q2 c2 ->
      eq_tm b1.binder_ty b2.binder_ty &&
      q1=q2 &&
      eq_comp c1 c2
    | Tm_While inv1 cond1 body1, Tm_While inv2 cond2 body2 ->
      eq_tm inv1 inv2 &&
      eq_tm cond1 cond2 &&
      eq_tm body1 body2
    | Tm_UVar z1, Tm_UVar z2 ->
      z1=z2
    | _ -> false
    
and eq_tm_opt (t1 t2:option term)
  : b:bool { b <==> (t1 == t2) }
  = match t1, t2 with
    | None, None -> true
    | Some t1, Some t2 -> eq_tm t1 t2
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
