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

  | Tm_UVar     : term -> int -> term

and binder = {
  binder_ty     : term;
  binder_ppname : string
}

and comp =
  | C_Tot : term -> comp
  | C_ST  : st_comp -> comp

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
    | Tm_VProp -> Set.empty
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
    | Tm_UVar t _ -> freevars t

and freevars_comp (c:comp) : Set.set var =
  match c with
  | C_Tot t -> freevars t
  | C_ST st -> freevars st.res `Set.union` freevars st.pre `Set.union` freevars st.post

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
  | Tm_VProp -> true

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

  | Tm_UVar t _ -> ln' t i

and ln'_comp (c:comp) (i:int)
  : Tot bool
  = match c with
    | C_Tot t -> ln' t i
    | C_ST st -> 
      ln' st.res i &&
      ln' st.pre i &&
      ln' st.post (i + 1) (* post has 1 impliict abstraction *)

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
    | Tm_Emp -> t

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

    | Tm_UVar t n -> Tm_UVar (open_term' t v i) n

and open_comp' (c:comp) (v:term) (i:index)
  : Tot comp (decreases c)
  = match c with
    | C_Tot t ->
      C_Tot (open_term' t v i)

    | C_ST c ->
      C_ST { c with res = open_term' c.res v i;
                    pre = open_term' c.pre v i;
                    post = open_term' c.post v (i + 1) }
    
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
    | Tm_Emp -> t

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

    | Tm_UVar t n -> Tm_UVar (close_term' t v i) n

and close_comp' (c:comp) (v:var) (i:index)
  : Tot comp (decreases c)
  = match c with
    | C_Tot t ->
      C_Tot (close_term' t v i)

    | C_ST c ->
      C_ST { c with res = close_term' c.res v i;
                    pre = close_term' c.pre v i;
                    post = close_term' c.post v (i + 1) }

let close_term t v = close_term' t v 0
let close_comp t v = close_comp' t v 0

let comp_res (c:comp) : term =
  match c with
  | C_Tot ty -> ty
  | C_ST c -> c.res

let comp_u (c:comp { C_ST? c }) = let C_ST s = c in s.u
let comp_pre (c:comp { C_ST? c }) = let C_ST s = c in s.pre
let comp_post (c:comp { C_ST? c }) = let C_ST s = c in s.post

let rec close_open_inverse (t:term) (x:var { ~(x `Set.mem` freevars t) } )
  : Lemma (ensures close_term (open_term t x) x== t)
          (decreases t)
  = admit()

// let constant_to_string (c:constant) : string =
//   match c with
//   | Unit -> "()"
//   | Bool b -> string_of_bool b
//   | Int n -> string_of_int n

// let rec term_to_string (t:term) : Tot string (decreases t) =
//   match t with
//   | Tm_BVar bv -> bv.bv_ppname ^ "@" ^ (string_of_int bv.bv_index)
//   | Tm_Var nm -> nm.nm_ppname ^ "#" ^ (string_of_int nm.nm_index)
//   | Tm_FVar l -> String.concat "." l
//   | Tm_Constant c -> constant_to_string c
//   | Tm_Abs b pre_hint body ->
//     "(" ^
//     "fun (" ^
//     (binder_to_string b) ^ ")_(" ^
//     (term_to_string pre_hint) ^ ") -> " ^
//     (term_to_string body) ^
//     ")"
//   | Tm_PureApp head arg ->
//     "(" ^
//     (term_to_string head) ^ " " ^ (term_to_string arg) ^
//     ")"
//   | Tm_Let _ _ _ -> "<Tm_Let>"
//   | Tm_STApp head arg ->
//     "(" ^
//     (term_to_string head) ^ " " ^ (term_to_string arg) ^
//     ")"
//   | Tm_Bind t e1 e2 ->
//     "let _:" ^ term_to_string t ^ " = " ^
//     term_to_string e1 ^ "; " ^ term_to_string e2
//   | Tm_Emp -> "emp"
//   | Tm_Pure p -> "pure (" ^ (term_to_string p) ^ ")"
//   | Tm_Star l r -> "star (" ^ (term_to_string l) ^ ") (" ^ (term_to_string r) ^ ")"
//   | _ -> "<term>"

// and binder_to_string (b:binder) : string =
//   b.binder_ppname ^ ":" ^ term_to_string (b.binder_ty)

let null_binder (t:term) : binder =
  {binder_ty=t;binder_ppname="_"}

let mk_binder (s:string) (t:term) : binder =
  {binder_ty=t;binder_ppname=s}

let mk_bvar (s:string) (i:index) : term =
  Tm_BVar {bv_index=i;bv_ppname=s}

let null_var (v:var) : term = Tm_Var {nm_index=v;nm_ppname="_"}

let null_bvar (i:index) : term = Tm_BVar {bv_index=i;bv_ppname="_"}

let gen_uvar (t:term) : T.Tac term =
  Tm_UVar t (T.fresh ())
