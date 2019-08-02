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

module StlcCbvDbPntSubstNoLists

type ty =
  | TArrow : t1:ty -> t2:ty -> ty

type var = nat

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : ty -> exp -> exp

val is_value : exp -> Tot bool
let is_value = EAbs?

(* subst_beta is a generalization of the substitution we do for the beta rule,
   when we've under x binders (useful for the substitution lemma) *)
(* This definition only works right for substituting _closed_ things
   (otherwise it captures the variables in v, giving a wrong semantics);
   this will be a problem when moving away from STLC! *)
val subst_beta : x:var -> v:exp -> e:exp -> Tot exp (decreases e)
let rec subst_beta x v e =
  match e with
  | EVar y ->      if y = x then v
              else if y < x then EVar y
              else               EVar (y-1)
  | EAbs t e1 -> EAbs t (subst_beta (x+1) v e1)
  | EApp e1 e2 -> EApp (subst_beta x v e1) (subst_beta x v e2)

val step : exp -> Tot (option exp)
let rec step e =
  match e with
  | EApp e1 e2 ->
      if is_value e1 then
        if is_value e2 then
          match e1 with
          | EAbs t e' -> Some (subst_beta 0 e2 e')
          | _         -> None
        else
          match (step e2) with
          | Some e2' -> Some (EApp e1 e2')
          | None     -> None
      else
        (match (step e1) with
        | Some e1' -> Some (EApp e1' e2)
        | None     -> None)
  | _ -> None

type env = var -> Tot (option ty)

val empty : env
let empty _ = None

val extend : env -> var -> ty -> Tot env
let extend g x t y = if y < x then g y
                     else if y = x then Some t
                     else g (y-1)

noeq type rtyping : env -> exp -> ty -> Type =
  | TyVar : #g:env ->
            x:var{Some? (g x)} ->
              rtyping g (EVar x) (Some?.v (g x))
  | TyAbs : #g:env ->
            t:ty ->
            #e1:exp ->
            #t':ty ->
            rtyping (extend g 0 t) e1 t' ->
            rtyping g (EAbs t e1) (TArrow t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:ty ->
            #t12:ty ->
            rtyping g e1 (TArrow t11 t12) ->
            rtyping g e2 t11 ->
            rtyping g (EApp e1 e2) t12

val progress : #e:exp -> #t:ty -> h:rtyping empty e t ->
      Lemma (requires True) (ensures (is_value e \/ (Some? (step e)))) (decreases h)
let rec progress #e #t h =
  match h with
  | TyVar _     -> ()
  | TyAbs _ _ -> ()
  | TyApp h1 h2 -> progress h1; progress h2

val appears_free_in : x:var -> e:exp -> Tot bool (decreases e)
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | EAbs _ e1 -> appears_free_in (x+1) e1

val free_in_context : x:var -> #e:exp -> #g:env -> #t:ty -> h:rtyping g e t ->
      Lemma (requires True) (ensures (appears_free_in x e ==> Some? (g x))) (decreases h)
let rec free_in_context x #e #g #t h =
  match h with
  | TyVar x -> ()
  | TyAbs t h1 -> free_in_context (x+1) h1
  | TyApp h1 h2 -> free_in_context x h1; free_in_context x h2

val typable_empty_closed : x:var -> #e:exp -> #t:ty -> rtyping empty e t ->
      Lemma (ensures (not(appears_free_in x e)))
(*      [SMTPat (appears_free_in x e)] -- CH: adding this makes it fail! *)
let typable_empty_closed x #e #t h = free_in_context x h

val typable_empty_closed' : #e:exp -> #t:ty -> rtyping empty e t ->
      Lemma (ensures (forall (x:var). (not(appears_free_in x e))))
let typable_empty_closed' #e #t h = admit() (* CH: need forall_intro for showing this *)

type equal (g1:env) (g2:env) =  forall (x:var). g1 x = g2 x
type equalE (e:exp) (g1:env) (g2:env) =
       forall (x:var). appears_free_in x e ==> g1 x = g2 x

val context_invariance : #e:exp -> #g:env -> #t:ty ->
      h:(rtyping g e t) -> g':env{equalE e g g'} ->
      Tot (rtyping g' e t) (decreases h)
let rec context_invariance #e #g #t h g' =
  match h with
  | TyVar x -> TyVar x
  | TyAbs t_y h1 ->
    TyAbs t_y (context_invariance h1 (extend g' 0 t_y))
  | TyApp h1 h2 ->
    TyApp (context_invariance h1 g') (context_invariance h2 g')

val typing_extensional : #e:exp -> #g:env -> #t:ty ->
      h:(rtyping g e t) -> g':env{equal g g'} ->
      Tot (rtyping g' e t)
let typing_extensional #e #g #t h g' = context_invariance h g'

val substitution_preserves_typing :
      x:var -> #e:exp -> #v:exp -> #t_x:ty -> #t:ty -> #g:env ->
      h1:rtyping empty v t_x ->
      h2:rtyping (extend g x t_x) e t ->
      Tot (rtyping g (subst_beta x v e) t) (decreases e)
let rec substitution_preserves_typing x #e #v #t_x #t #g h1 h2 =
  match h2 with
  | TyVar y ->
     if x=y then      (typable_empty_closed' h1; context_invariance h1 g)
     else if y<x then context_invariance h2 g
     else             TyVar (y-1)
  | TyAbs #g' t_y #e' #t' h21 ->
     (let h21' = typing_extensional h21 (extend (extend g 0 t_y) (x+1) t_x) in
      TyAbs t_y (substitution_preserves_typing (x+1) h1 h21'))
  | TyApp #g' #e1 #e2 #t11 #t12 h21 h22 ->
     (* CH: implicits don't work here, why? *)
     (* NS: They do now *)
    (TyApp // #g #(subst_beta x v e1) #(subst_beta x v e2) #t11 #t12
       (substitution_preserves_typing x h1 h21)
       (substitution_preserves_typing x h1 h22))

val preservation : #e:exp -> #t:ty -> h:rtyping empty e t{Some? (step e)} ->
      Tot (rtyping empty (Some?.v (step e)) t) (decreases e)
let rec preservation #e #t h =
  let TyApp #g #e1 #e2 #t11 #t12 h1 h2 = h in
     if is_value e1
     then (if is_value e2
           then let TyAbs t_x hbody = h1 in
                substitution_preserves_typing 0 h2 hbody
           else TyApp h1 (preservation h2)) 
                           //^^^^^^^^^^^^^^^^^
     else TyApp (preservation h1) h2
