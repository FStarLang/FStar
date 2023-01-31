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

noeq
type term =
  // | Tm_Embed    : R.term -> term // a host term included as is in Pulse
  | Tm_BVar     : bv -> term
  | Tm_Var      : nm -> term
  | Tm_FVar     : l:R.name -> term
  | Tm_UInst    : l:R.name -> us:list universe -> term
  | Tm_Constant : c:constant -> term
  | Tm_Refine   : b:binder -> term -> term
  | Tm_Abs      : b:binder -> q:option qualifier -> pre_hint:vprop -> body:term -> opost:option vprop -> term  //pre and post hints
  | Tm_PureApp  : head:term -> arg_qual:option qualifier -> arg:term -> term
  | Tm_Let      : t:term -> e1:term -> e2:term -> term  
  | Tm_STApp    : head:term -> arg_qual:option qualifier -> arg:term -> term  
  | Tm_Bind     : e1:term -> e2:term -> term
  | Tm_Emp      : term
  | Tm_Pure     : p:term -> term (* pure p : vprop *)
  | Tm_Star     : l:vprop -> r:vprop -> term
  | Tm_ExistsSL : t:term -> body:vprop -> term
  | Tm_ForallSL : t:term -> body:vprop -> term
  | Tm_Arrow    : b:binder -> q:option qualifier -> body:comp -> term 
  | Tm_Type     : universe -> term
  | Tm_VProp    : term
  | Tm_If       : b:term -> then_:term -> else_:term -> term

  | Tm_Inames   : term  // type inames
  | Tm_EmpInames: term
  // | Tm_Inv      : term -> term
  // | Tm_AddInv   : term -> term -> term

  | Tm_UVar     : int -> term

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
    | Tm_Abs b _ _ body _ -> Set.union (freevars b.binder_ty) (freevars body)  // Why is this not taking freevars of pre (and post)?
    | Tm_PureApp t1 _ t2
    | Tm_STApp t1 _ t2
    | Tm_Star  t1 t2
    | Tm_ExistsSL t1 t2
    | Tm_ForallSL t1 t2 
    | Tm_Bind t1 t2 -> Set.union (freevars t1) (freevars t2)

    | Tm_Let t e1 e2
    | Tm_If t e1 e2 ->
      Set.union (Set.union (freevars t) (freevars e1)) (freevars e2)

    | Tm_Pure p -> freevars p

    | Tm_Arrow b _ body -> Set.union (freevars b.binder_ty) (freevars_comp body)

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
  | Tm_Star t1 t2
  | Tm_Bind t1 t2 ->
    ln' t1 i &&
    ln' t2 i

  | Tm_Let t e1 e2 ->
    ln' t i &&
    ln' e1 i &&
    ln' e2 (i + 1)

  | Tm_Pure p ->
    ln' p i

  | Tm_ExistsSL t body
  | Tm_ForallSL t body ->
    ln' t i &&
    ln' t (i + 1)
    
  | Tm_Arrow b _ c ->
    ln' b.binder_ty i &&
    ln'_comp c (i + 1)
    
  | Tm_If b then_ else_ ->
    ln' b i &&
    ln' then_ i &&
    ln' else_ i

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
    // | Tm_Embed t -> 
    //   Tm_Embed (RT.open_or_close_term' t ??? *)
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
              
    | Tm_ExistsSL t body ->
      Tm_ExistsSL (open_term' t v i)
                  (open_term' body v (i + 1))
                  
    | Tm_ForallSL t body ->
      Tm_ForallSL (open_term' t v i)
                  (open_term' body v (i + 1))
    
    | Tm_Arrow b q c ->
      Tm_Arrow {b with binder_ty=open_term' b.binder_ty v i} q
               (open_comp' c v (i + 1))

    | Tm_If b then_ else_ ->
      Tm_If (open_term' b v i)
            (open_term' then_ v i)
            (open_term' else_ v i)


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
  open_term' t (Tm_Var {nm_ppname="x";nm_index=v}) 0
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
              
    | Tm_ExistsSL t body ->
      Tm_ExistsSL (close_term' t v i)
                  (close_term' body v (i + 1))
                  
    | Tm_ForallSL t body ->
      Tm_ForallSL (close_term' t v i)
                  (close_term' body v (i + 1))
    
    | Tm_Arrow b q c ->
      Tm_Arrow {b with binder_ty=close_term' b.binder_ty v i} q
               (close_comp' c v (i + 1))

    | Tm_If b then_ else_ ->
      Tm_If (close_term' b v i)
            (close_term' then_ v i)
            (close_term' else_ v i)

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

let rec close_open_inverse (t:term) (x:var { ~(x `Set.mem` freevars t) } )
  : Lemma (ensures close_term (open_term t x) x== t)
          (decreases t)
  = admit()

let null_binder (t:term) : binder =
  {binder_ty=t;binder_ppname="x"}

let mk_binder (s:string) (t:term) : binder =
  {binder_ty=t;binder_ppname=s}

let mk_bvar (s:string) (i:index) : term =
  Tm_BVar {bv_index=i;bv_ppname=s}

let null_var (v:var) : term = Tm_Var {nm_index=v;nm_ppname="x"}

let null_bvar (i:index) : term = Tm_BVar {bv_index=i;bv_ppname="x"}

let gen_uvar (t:term) : T.Tac term =
  Tm_UVar (T.fresh ())

let rec eq_tm (t1 t2:term) : bool =
  match t1, t2 with
  | Tm_BVar bv1, Tm_BVar bv2 -> bv1.bv_index = bv2.bv_index
  | Tm_Var nm1, Tm_Var nm2 -> nm1.nm_index = nm2.nm_index
  | Tm_FVar l1, Tm_FVar l2 -> l1 = l2
  | Tm_UInst l1 us1, Tm_UInst l2 us2 -> l1 = l2 && us1 = us2
  | Tm_Constant c1, Tm_Constant c2 -> c1 = c2
  | Tm_Refine b1 t1, Tm_Refine b2 t2 ->
    eq_binder b1 b2 &&
    eq_tm t1 t2
  | Tm_Abs b1 q1 pre1 body1 opost1, Tm_Abs b2 q2 pre2 body2 opost2 ->
    eq_binder b1 b2 &&
    q1 = q1 &&
    eq_tm pre1 pre2 &&
    eq_tm body1 body2 &&
    eq_tm_opt opost1 opost2
  | Tm_PureApp head1 q1 arg1, Tm_PureApp head2 q2 arg2
  | Tm_STApp head1 q1 arg1, Tm_STApp head2 q2 arg2 ->
    eq_tm head1 head2 &&
    q1 = q2 &&
    eq_tm arg1 arg2
  | Tm_Let t1 e11 e12, Tm_Let t2 e21 e22 ->
    eq_tm t1 t2 &&
    eq_tm e11 e21 &&
    eq_tm e12 e22
  | Tm_Bind e1 e2, Tm_Bind e3 e4 ->
    eq_tm e1 e3 &&
    eq_tm e2 e4
  | Tm_Emp, Tm_Emp -> true
  | Tm_Pure p1, Tm_Pure p2 -> eq_tm p1 p2
  | Tm_Star l1 r1, Tm_Star l2 r2 ->
    eq_tm l1 l2 &&
    eq_tm r1 r2
  | Tm_ExistsSL t1 body1, Tm_ExistsSL t2 body2
  | Tm_ForallSL t1 body1, Tm_ForallSL t2 body2 ->
    eq_tm t1 t2 &&
    eq_tm body1 body2
  | Tm_Arrow b1 q1 c1, Tm_Arrow b2 q2 c2 ->
    eq_binder b1 b2 &&
    q1 = q2 &&
    eq_comp c1 c2
  | Tm_Type u1, Tm_Type u2 -> u1 = u2
  | Tm_VProp, Tm_VProp -> true
  | Tm_If b1 t_then1 t_else1, Tm_If b2 t_then2 t_else2 ->
    eq_tm b1 b2 &&
    eq_tm t_then1 t_then2 &&
    eq_tm t_else1 t_else2
  | Tm_Inames, Tm_Inames -> true
  | Tm_EmpInames, Tm_EmpInames -> true
  | Tm_UVar n1, Tm_UVar n2 -> n1 = n2
  | _, _ -> false

and eq_tm_opt (t1 t2:option term) : bool =
  match t1, t2 with
  | None, None -> true
  | Some t1, Some t2 -> eq_tm t1 t2
  | _, _ -> false

and eq_binder (b1 b2:binder) : bool = eq_tm b1.binder_ty b2.binder_ty
and eq_comp (c1 c2:comp) : bool =
  match c1, c2 with
  | C_Tot t1, C_Tot t2 -> eq_tm t1 t2
  | C_ST s1, C_ST s2 -> eq_st_comp s1 s2
  | C_STAtomic inames1 s1, C_STAtomic inames2 s2
  | C_STGhost inames1 s1, C_STGhost inames2 s2 ->
    eq_tm inames1 inames2 &&
    eq_st_comp s1 s2
  | _, _ -> false

and eq_st_comp (s1 s2:st_comp) : bool =
  s1.u = s2.u &&
  eq_tm s1.res s2.res &&
  eq_tm s1.pre s2.pre &&
  eq_tm s1.post s2.post
