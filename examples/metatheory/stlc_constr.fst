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

module StlcConstr

type ty =
  | TArrow : t1:ty -> t2:ty -> ty

type exp =
  | EVar   : int -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : int -> ty -> exp -> exp

val is_value : exp -> Tot bool
let is_value = is_EAbs

val subst : int -> exp -> exp -> Tot exp
let rec subst x e e' =
  match e' with
  | EVar x' -> if x = x' then e else e'
  | EAbs x' t e1 ->
      EAbs x' t (if x = x' then e1 else (subst x e e1))
  | EApp e1 e2 -> EApp (subst x e e1) (subst x e e2)

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
      else
        (match (step e1) with
        | Some e1' -> Some (EApp e1' e2)
        | None     -> None)
  | _ -> None

type env = int -> Tot (option ty)

val empty : env
let empty _ = None

val extend : env -> int -> ty -> Tot env
let extend g x t x' = if x = x' then Some t else g x'

type rtyping : env -> exp -> ty -> Type =
  | TyVar : #g:env ->
            x:int{is_Some (g x)} ->
              rtyping g (EVar x) (Some.v (g x))
  | TyAbs : #g:env ->
            x:int ->
            t:ty ->
            #e1:exp ->
            #t':ty ->
            rtyping (extend g x t) e1 t' ->
            rtyping g (EAbs x t e1) (TArrow t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:ty ->
            #t12:ty ->
            rtyping g e1 (TArrow t11 t12) ->
            rtyping g e2 t11 ->
            rtyping g (EApp e1 e2) t12

val progress : #e:exp -> #t:ty -> h:rtyping empty e t ->
      Lemma (ensures (is_value e \/ (is_Some (step e)))) (decreases h)
let rec progress _ _ h =
  match h with
  | TyVar _     -> ()
  | TyAbs _ _ _ -> ()
  | TyApp h1 h2 -> progress h1; progress h2

val appears_free_in : x:int -> e:exp -> Tot bool
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | EAbs y _ e1 -> x <> y && appears_free_in x e1

val free_in_context : x:int -> #e:exp -> #g:env -> #t:ty -> h:rtyping g e t ->
      Lemma (ensures (appears_free_in x e ==> is_Some (g x))) (decreases h)
let rec free_in_context x _ _ _ h =
  match h with
  | TyVar x -> ()
  | TyAbs y t h1 -> free_in_context x h1
  | TyApp h1 h2 -> free_in_context x h1; free_in_context x h2

val typable_empty_closed : x:int -> #e:exp -> #t:ty -> rtyping empty e t ->
      Lemma (ensures (not(appears_free_in x e)))
(*      [SMTPat (appears_free_in x e)] -- CH: adding this makes it fail! *)
let typable_empty_closed x _ _ h = free_in_context x h

val typable_empty_closed' : #e:exp -> #t:ty -> rtyping empty e t ->
      Lemma (ensures (forall (x:int). (not(appears_free_in x e))))
let typable_empty_closed' _ _ h = admit() (* CH: need forall_intro for showing this *)

opaque logic type Equal (g1:env) (g2:env) =
                 (forall (x:int). g1 x=g2 x)
opaque logic type EqualE (e:exp) (g1:env) (g2:env) =
                 (forall (x:int). appears_free_in x e ==> g1 x=g2 x)

val context_invariance : #e:exp -> #g:env -> #t:ty -> 
      h:(rtyping g e t) -> g':env{EqualE e g g'} ->
      Tot (rtyping g' e t) (decreases h)
let rec context_invariance _ _ _ h g' =
  match h with
  | TyVar x -> TyVar x
  | TyAbs y t_y h1 ->
    TyAbs y t_y (context_invariance h1 (extend g' y t_y))
  | TyApp h1 h2 ->
    TyApp (context_invariance h1 g') (context_invariance h2 g')

val typing_extensional : #e:exp -> #g:env -> #t:ty ->
      h:(rtyping g e t) -> g':env{Equal g g'} ->
      Tot (rtyping g' e t)
let typing_extensional _ _ _ h g' = context_invariance h g'

(* CH: would it be possible to prove this with x implicit? maybe not ... *)
val substitution_preserves_typing :
      x:int -> #e:exp -> #v:exp -> #t_x:ty -> #t:ty -> #g:env ->
      h1:rtyping empty v t_x ->
      h2:rtyping (extend g x t_x) e t ->
      Tot (rtyping g (subst x v e) t) (decreases e)
let rec substitution_preserves_typing x _ v t_x t g h1 h2 =
  match h2 with
  | TyVar y ->
     if x=y
     then (typable_empty_closed' h1; context_invariance h1 g)
     else context_invariance h2 g
  | TyAbs y t_y h21 ->
     let gy = extend g y t_y in
     if x=y
     then TyAbs y t_y (typing_extensional h21 gy)
     else
       (let h21' = typing_extensional h21 (extend gy x t_x) in
        TyAbs y t_y (substitution_preserves_typing x h1 h21'))
  | TyApp #g' #e1 #e2 #t11 #t12 h21 h22 -> (* CH: implicits don't work here, why? *)
     TyApp #g #(subst x v e1) #(subst x v e2) #t11 #t12
       (substitution_preserves_typing x h1 h21)
       (substitution_preserves_typing x h1 h22)

val preservation : #e:exp{is_Some (step e)} -> #t:ty -> h:(rtyping empty e t) ->
      Tot (rtyping empty (Some.v (step e)) t) (decreases e)
let rec preservation e t h =
  let TyApp #g #e1 #e2 #t11 #t12 h1 h2 = h in
     if is_value e1
     then (if is_value e2
           then let TyAbs x t_x hbody = h1 in
                substitution_preserves_typing x h2 hbody
           else TyApp h1 (preservation h2))
     else TyApp (preservation h1) h2
