module Pulse.Syntax
module RT = Refl.Typing
module R = FStar.Reflection
open FStar.List.Tot

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
   but it doesn't have to be. and if we include Embed it won't be. 
   So, we should remove reliance on this thing being an eqtype soon.
*)
type term =
(*  | Embed  of R.term *)
  | Tm_BVar     : i:index -> term
  | Tm_Var      : v:var -> term
  | Tm_FVar     : l:R.name -> term
  | Tm_Constant : c:constant -> term
  | Tm_Abs      : t:term -> pre_hint:vprop -> body:term -> term
  | Tm_PureApp  : head:term -> arg:term -> term
  | Tm_Let      : t:term -> e1:term -> e2:term -> term  
  | Tm_STApp    : head:term -> arg:term -> term  
  | Tm_Bind     : t:term -> e1:term -> e2:term -> term
  | Tm_Emp      : term
  | Tm_Pure     : p:term -> term (* pure p : vprop *)
  | Tm_Star     : l:vprop -> r:vprop -> term
  | Tm_ExistsSL : t:term -> body:vprop -> term
  | Tm_ForallSL : t:term -> body:vprop -> term
  | Tm_Arrow    : t:term -> body:comp -> term 
  | Tm_Type     : universe -> term
  | Tm_VProp    : term
  | Tm_If       : b:term -> then_:term -> else_:term -> term

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


assume
val freevars (t:term) : Set.set var

let freevars_comp (c:comp) : Set.set var =
  match c with
  | C_Tot t -> freevars t
  | C_ST st -> freevars st.res `Set.union` freevars st.pre `Set.union` freevars st.post

let rec ln' (t:term) (i:int) =
  match t with
  | Tm_BVar j -> j <= i
  | Tm_Var _
  | Tm_FVar _
  | Tm_Constant _  
  | Tm_Emp
  | Tm_Type _
  | Tm_VProp -> true

  | Tm_Abs t pre_hint body ->
    ln' t i &&
    ln' pre_hint (i + 1) &&
    ln' body (i + 1)

  | Tm_STApp t1 t2
  | Tm_PureApp t1 t2
  | Tm_Star t1 t2 ->
    ln' t1 i &&
    ln' t2 i

  | Tm_Let t e1 e2
  | Tm_Bind t e1 e2 ->
    ln' t i &&
    ln' e1 i &&
    ln' e2 (i + 1)

  | Tm_Pure p ->
    ln' p i

  | Tm_ExistsSL t body
  | Tm_ForallSL t body ->
    ln' t i &&
    ln' t (i + 1)
    
  | Tm_Arrow t c ->
    ln' t i &&
    ln'_comp c (i + 1)
    
  | Tm_If b then_ else_ ->
    ln' b i &&
    ln' then_ i &&
    ln' else_ i

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
    | Tm_BVar j -> if i = j then v else t

    | Tm_Var _
    | Tm_FVar _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Emp -> t

    | Tm_Abs t pre_hint body ->
      Tm_Abs (open_term' t v i)
             (open_term' pre_hint v i)
             (open_term' body v (i + 1))

    | Tm_PureApp head arg ->
      Tm_PureApp (open_term' head v i)
                 (open_term' arg v i)
                 
    | Tm_Let t e1 e2 ->
      Tm_Let (open_term' t v i)
             (open_term' e1 v i)
             (open_term' e2 v (i + 1))
             
    | Tm_STApp head arg ->
      Tm_STApp (open_term' head v i)
               (open_term' arg v i)

    | Tm_Bind t e1 e2 ->
      Tm_Bind (open_term' t v i)
              (open_term' e1 v i)
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
    
    | Tm_Arrow t c ->
      Tm_Arrow (open_term' t v i)
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

    | C_ST c ->
      C_ST { c with res = open_term' c.res v i;
                    pre = open_term' c.pre v i;
                    post = open_term' c.post v (i + 1) }
    
let open_term t v = open_term' t (Tm_Var v) 0
let open_comp_with (c:comp) (x:term) = open_comp' c x 0

let rec close_term' (t:term) (v:var) (i:index)
  : term
  = match t with
    | Tm_Var m -> if m = v then Tm_BVar i else t
    
    | Tm_BVar _
    | Tm_FVar _
    | Tm_Constant _
    | Tm_Type _
    | Tm_VProp
    | Tm_Emp -> t

    | Tm_Abs t pre_hint body ->
      Tm_Abs (close_term' t v i)
             (close_term' pre_hint v i)
             (close_term' body v (i + 1))

    | Tm_PureApp head arg ->
      Tm_PureApp (close_term' head v i)
                 (close_term' arg v i)
                 
    | Tm_Let t e1 e2 ->
      Tm_Let (close_term' t v i)
             (close_term' e1 v i)
             (close_term' e2 v (i + 1))
             
    | Tm_STApp head arg ->
      Tm_STApp (close_term' head v i)
               (close_term' arg v i)

    | Tm_Bind t e1 e2 ->
      Tm_Bind (close_term' t v i)
              (close_term' e1 v i)
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
    
    | Tm_Arrow t c ->
      Tm_Arrow (close_term' t v i)
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
