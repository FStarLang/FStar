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
let rec is_value e =
  match e with
  | EAbs _ _ _  -> true
  | _           -> false

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
  | TyVar : g:env ->
            x:int{is_Some (g x)} ->
              rtyping g (EVar x) (Some.v (g x))
  | TyAbs : g:env ->
            x:int ->
            t:ty ->
            e1:exp ->
            t':ty ->
            rtyping (extend g x t) e1 t' ->
            rtyping g (EAbs x t e1) (TArrow t t')
  | TyApp : g:env ->
            e1:exp ->
            e2:exp ->
            t11:ty ->
            t12:ty ->
            rtyping g e1 (TArrow t11 t12) ->
            rtyping g e2 t11 ->
            rtyping g (EApp e1 e2) t12

val progress : #e:exp -> #t:ty ->
               rtyping empty e t ->
               Lemma (ensures (is_value e \/ (is_Some (step e))))
let rec progress e t h =
  match h with
  | TyVar g x -> ()
  | TyAbs g x t e1 t' h1 -> ()
  | TyApp g e1 e2 t11 t12 h1 h2 -> progress h1; progress h2

