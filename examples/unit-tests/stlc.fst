(*
   Copyright 2008-2014 Catalin Hritcu, Nikhil Swamy, Microsoft Research and Inria

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Stlc
open Prims.PURE

type ty =
  | TBool  : ty
  | TArrow : ty -> ty -> ty

type exp =
  | EVar   : int -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : int -> ty -> exp -> exp
  | ETrue  : exp
  | EFalse : exp
  | EIf    : exp -> exp -> exp -> exp

val is_value : exp -> Tot bool
let is_value e =
  match e with
  | EAbs _ _ _ -> true
  | ETrue      -> true
  | EFalse     -> true
  | _          -> false

(* Because we only consider call-by-value reduction, we will ever only
   substitute closed values, so this definition of substitution is
   good enough *)
val subst : int -> exp -> exp -> Tot exp
let rec subst x e e' =
  match e' with
  | EVar x' -> if x = x' then e else e'
  | EAbs x' t e1 ->
      EAbs x' t (if x = x' then e1 else (subst x e e1))
  | EApp e1 e2 -> EApp (subst x e e1) (subst x e e2)
  | ETrue -> ETrue
  | EFalse -> EFalse
  | EIf e1 e2 e3 -> EIf (subst x e e1) (subst x e e2) (subst x e e3)

val step : exp -> Tot (option exp)
let rec step e =
  match e with
  | EApp e1 e2 ->
      if is_value e1 then
        if is_value e2 then
          match e1 with
          | EAbs x t e' -> Some (subst x e2 e')
          | _           -> None
        else
          match (step e2) with
          | Some e2' -> Some (EApp e1 e2')
          | None     -> None
      else begin
        match (step e1) with
        | Some e1' -> Some (EApp e1' e2)
        | None     -> None
      end
  | EIf e1 e2 e3 ->
      if is_value e1 then
        match e1 with
        | ETrue   -> Some e2
        | EFalse  -> Some e3
        | _       -> None
      else begin
        match (step e1) with
        | Some e1' -> Some (EIf e1' e2 e3)
        | None     -> None
      end
  | _ -> None

type env = int -> Tot (option ty)

val empty : env
let empty _ = None

val extend : env -> int -> ty -> Tot env
let extend g x t x' = if x = x' then Some t else g x'

val append: env -> env -> Tot env
let append g1 g2 x = match g2 x with 
  | None -> g1 x
  | found -> found

val extend_eq : g:env -> x:int -> a:ty -> Theorem 
      (requires True)
      (ensures ((extend g x a) x) = Some a)
let extend_eq g x a = ()

val extend_neq : g:env -> x1:int -> a:ty -> x2:int -> Theorem 
      (requires (x1 <> x2))
      (ensures ((extend g x1 a) x2) = g x2)
let extend_neq g x1 a x2 = ()

(* CH: swapped env and exp args until functions are ignored from the
   lex ordering or until we can write decreasing clauses *)
val typing : exp -> env -> Tot (option ty)
let rec typing e g =
  match e with
  | EVar x -> g x
  | EAbs x t e1 -> begin
      match typing e1 (extend g x t) with
      | Some t' -> Some (TArrow t t')
      | None    -> None
      end
  | EApp e1 e2 -> begin
      match typing e1 g, typing e2 g with
      | Some (TArrow t11 t12), Some t2 -> if t11 = t2 then Some t12 else None
      | _                    , _       -> None
      end
  | ETrue  -> Some TBool
  | EFalse -> Some TBool
  | EIf e1 e2 e3 -> begin
      match typing e1 g, typing e2 g, typing e3 g with
      | Some TBool, Some t2, Some t3 -> if t2 = t3 then Some t2 else None
      | _         , _      , _       -> None
       end

val canonical_forms_bool : e:exp -> Theorem 
      (requires (typing e empty=Some TBool /\ is_value e))
      (ensures (is_ETrue e \/ is_EFalse e))
let canonical_forms_bool e = ()

val canonical_forms_fun : e:exp -> t1:ty -> t2:ty -> Theorem 
      (requires (typing e empty == Some (TArrow t1 t2) /\ is_value e))
      (ensures (is_EAbs e))
let canonical_forms_fun e t1 t2 = ()

val sel_empty : x:int -> Theorem 
      (requires True)
      (ensures (is_None (empty x)))
let sel_empty x = ()

val progress : e:exp -> t:ty -> Theorem 
      (requires (typing e empty == Some t))
      (ensures (is_value e \/ (is_Some (step e))))
let rec progress e t =
  match e with
  | EApp e1 e2 -> 
     let Some (TArrow t1 t2) = typing e1 empty in
     progress e1 (TArrow t1 t2); 
     progress e2 t1
  | EIf e1 e2 e3 ->
     progress e1 TBool;
     progress e2 t; 
     progress e3 t
  | _ -> () 

val appears_free_in : x:int -> e:exp -> Tot bool
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | EAbs y _ e1 -> x <> y && appears_free_in x e1
  | EIf e1 e2 e3 ->
      appears_free_in x e1 || appears_free_in x e2 || appears_free_in x e3
  | ETrue
  | EFalse -> false (* NS: writing default cases for recursive functions is bad for the solver. TODO: fix *)

val free_in_context : x:int -> e:exp -> g:env 
                   -> Theorem 
                        (requires (appears_free_in x e /\ is_Some (typing e g)))
                        (ensures (is_Some (g x)))
let rec free_in_context x e g =
  match e with
  | EAbs y t e1 -> 
     if x = y 
     then ()
     else free_in_context x e1 (extend g y t)

  | EApp e1 e2 -> 
     if appears_free_in x e1
     then free_in_context x e1 g
     else free_in_context x e2 g

  | EIf e1 e2 e3 -> 
     if      appears_free_in x e1 then free_in_context x e1 g
     else if appears_free_in x e2 then free_in_context x e2 g
     else                              free_in_context x e3 g

  | _ -> ()

opaque logic type Equal (g1:env) (g2:env) = 
                 (forall (x:int). g1 x=g2 x)
opaque logic type EqualE (e:exp) (g1:env) (g2:env) = 
                 (forall (x:int). appears_free_in x e ==> g1 x=g2 x)

val context_invariance : e:exp -> g:env -> g':env 
                     -> Theorem 
                          (requires (EqualE e g g'))
                          (ensures (typing e g == typing e g'))
let rec context_invariance e g g' =
  match e with
  | EAbs x t e1 -> 
     context_invariance e1 (extend g x t) (extend g' x t) 

  | EApp e1 e2 -> 
     context_invariance e1 g g';
     context_invariance e2 g g'

  | EIf e1 e2 e3 ->
     context_invariance e1 g g';
     context_invariance e2 g g';
     context_invariance e3 g g'

  | _ -> ()

val typing_extensional : g:env -> g':env -> e:exp 
                      -> Theorem 
                           (requires (Equal g g'))
                           (ensures (typing e g == typing e g'))
let typing_extensional g g' e = context_invariance e g g' 
                        
(* Corollary of free_in_context *)
val typable_empty_closed : x:int -> e:exp -> Lemma
      (requires (is_Some (typing e empty) /\ appears_free_in x e))
      (ensures False)
      ([VPat (appears_free_in x e)])
let typable_empty_closed x e = free_in_context x e empty

val substitution_preserves_typing :
      x:int -> t_x:ty -> e:exp -> t_e:ty -> v:exp -> g1:env -> g2:env 
      -> Theorem 
          (requires ((typing e (append (extend g1 x t_x) g2) == Some t_e)
                     /\ is_None (g2 x)
                     /\ typing v empty == Some t_x))
          (ensures  (typing (subst x v e) (append g1 g2) == Some t_e))
let rec substitution_preserves_typing x t_x e t_e v g1 g2 =
  let g1g2 = append g1 g2 in
  let g1xg2 = append (extend g1 x t_x) g2 in
  match e with
  | ETrue -> ()
  | EFalse -> ()
  | EVar x' ->
     if x=x'
     then context_invariance v empty (append g1 g2) (* uses lemma typable_empty_closed *)
     else context_invariance e g1xg2 g1g2 (* no substitution, but need to show that x:t_x is removable *)
                             
  | EApp e1 e2 ->
     let Some (TArrow t1 t2) = typing e1 (append (extend g1 x t_x) g2) in
     substitution_preserves_typing x t_x e1 (TArrow t1 t2) v g1 g2;
     substitution_preserves_typing x t_x e2 t1 v g1 g2

  | EIf e1 e2 e3 ->
     substitution_preserves_typing x t_x e1 TBool v g1 g2;
     substitution_preserves_typing x t_x e2 t_e v g1 g2;
     substitution_preserves_typing x t_x e3 t_e v g1 g2

  | EAbs x' t' e1 ->
     let TArrow _ t_e1 = t_e in
     let g1xg2_x' = extend g1xg2 x' t' in
     let g1g2_x' = extend g1g2 x' t' in
     if x=x'
     then typing_extensional g1xg2_x' g1g2_x' e1
     else
       (typing_extensional g1xg2_x' (append (extend g1 x t_x) (extend g2 x' t')) e1;
        substitution_preserves_typing x t_x e1 t_e1 v g1 (extend g2 x' t');
        typing_extensional (append g1 (extend g2 x' t')) g1g2_x' (subst x v e1))
              
val preservation : e:exp -> e':exp -> t:ty 
                -> Theorem 
                     (requires (typing e empty == Some t /\ step e == Some e'))
                     (ensures (typing e' empty == Some t))
let rec preservation e e' t =
  match e with
  | EApp e1 e2 -> 
     let Some t1 = typing e1 empty in
     if is_value e1 
     then let TArrow targ _ = t1 in
          (if is_value e2 
           then let EAbs x _ ebody = e1 in
                typing_extensional (extend empty x targ) (append (extend empty x targ) empty) ebody;
                substitution_preserves_typing x targ ebody t e2 empty empty;
                typing_extensional (append empty empty) empty (subst x e2 ebody)
           else preservation e2 (Some.v (step e2)) targ)
     else preservation e1 (Some.v (step e1)) t1
                       
  | EIf e1 _ _ ->
      if is_value e1 
      then ()
      else preservation e1 (Some.v (step e1)) TBool
