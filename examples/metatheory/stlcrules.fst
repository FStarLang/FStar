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

module StlcRules

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

(* CH: writing this by hand for now *)
assume val rtyping_app : g:env ->
            e1:exp ->
            e2:exp ->
            t11:ty ->
            t12:ty -> Lemma
  (requires (rtyping g e1 (TArrow t11 t12) /\ rtyping g e2 t11))
  (ensures (rtyping g (EApp e1 e2) t12))
assume val rtyping_inv : g:env -> e:exp -> t:ty ->
  Lemma (requires (rtyping g e t))
        (ensures ((exists (x:int). e = EVar x /\ is_Some (g x)
                                /\ t = (Some.v (g x))) \/
                  (exists (x:int). exists (t_x:ty). exists (e1:exp). exists (t':ty).
                          e = EAbs x t e1 /\ t = TArrow t_x t' /\
                          rtyping (extend g x t_x) e1 t') \/
                  (exists (e1:exp). exists (e2:exp). exists (t11:ty).
                          e = EApp e1 e2 /\ rtyping g e1 (TArrow t11 t) /\
                                            rtyping g e2 t11)))
(* 
  [SMTPat (rtyping g e t)] -- causes "Failed to solve the sub-problem ..."
*)

(* trivial with only arrow types, all values are lambdas *)
val canonical_forms_fun : e:exp -> t1:ty -> t2:ty -> Lemma
      (requires (rtyping empty e (TArrow t1 t2) /\ is_value e))
      (ensures (is_EAbs e))
let canonical_forms_fun e t1 t2 = ()

(* CH: we need to make pre, post, and maybe also a implicit;
   without that this is a complete pain to use;
   unfortunately F* can't properly infer these things currently *)
(* CH: I would also write the {exists (x:a). p x} refinement directly
   on f instead of adding a spurious unit, unfortunately that causes
   a bogus error *)
assume val exists_elim :
  #pre:Type -> #post:(unit->Type) -> #a:Type -> p:(a->Type) ->
  u:unit{exists (x:a). p x} -> f:(x:a{p x} -> Pure unit pre post) ->
  Pure unit pre post

val progress : e:exp -> t:ty -> Lemma
      (requires (rtyping empty e t))
      (ensures (is_value e \/ (is_Some (step e))))
      (decreases e)
let rec progress e t =
  rtyping_inv empty e t;
  match e with
  | EVar _
  | EAbs _ _ _ -> ()
  | EApp e1 e2 ->
     exists_elim
       #(rtyping empty e t)
       #(fun _ -> is_value e \/ (is_Some (step e)))
       #ty
       (fun (t11:ty) -> rtyping empty e1 (TArrow t11 t)) ()
       (fun t11 ->
          progress e1 (TArrow t11 t);
          (* assert(rtyping empty e2 t11);
             -- it can't prove this (needed for calling progress e2 t11)
               but it can prove the above one, very strange *)
          admit()
       )

(*

val appears_free_in : x:int -> e:exp -> Tot bool
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | EAbs y _ e1 -> x <> y && appears_free_in x e1

val free_in_context : x:int -> e:exp -> g:env -> t:ty -> Lemma
      (requires (rtyping g e t))
      (ensures (appears_free_in x e ==> is_Some (g x)))
      (decreases e)
let rec free_in_context x e g t =
  match e with
  | EVar _ -> ()
  | EAbs y t_y e1 -> 
     admit()
     (* free_in_context x e1 (extend g y t_y) (TArrow t_y t) *)
  | EApp e1 e2 -> admit()
     (* free_in_context x e1 g; free_in_context x e2 g *)

(* Corollary of free_in_context when g=empty -- fed to the SMT solver *)
val typable_empty_closed : x:int -> e:exp -> t:ty -> Lemma
      (requires (rtyping empty e t))
      (ensures (not(appears_free_in x e)))
      [SMTPat (appears_free_in x e)]
let typable_empty_closed x e t = free_in_context x e empty t

opaque logic type Equal (g1:env) (g2:env) =
                 (forall (x:int). g1 x=g2 x)
opaque logic type EqualE (e:exp) (g1:env) (g2:env) =
                 (forall (x:int). appears_free_in x e ==> g1 x=g2 x)

val context_invariance : e:exp -> g:env -> g':env -> t:ty
                     -> Lemma
                          (requires (EqualE e g g'))
                          (ensures (rtyping g e t <==> rtyping g' e t))
let rec context_invariance e g g' t =
  match e with
  | EAbs x t e1 ->
     context_invariance e1 (extend g x t) (extend g' x t)

  | EApp e1 e2 ->
     context_invariance e1 g g';
     context_invariance e2 g g'

  | EVar _ -> ()

val typing_extensional : g:env -> g':env -> e:exp -> t:ty
                      -> Lemma
                           (requires (Equal g g'))
                           (ensures (rtyping g e t <==> rtyping g' e t))
let typing_extensional g g' e t = context_invariance e g g' t

val substitution_preserves_typing : x:int -> e:exp -> v:exp -> t_x:ty -> t:ty ->
      g:env{rtyping empty v t_x &&
            rtyping (extend g x t_x) e t} ->
      Tot (u:unit{rtyping g (subst x v e) t})
let rec substitution_preserves_typing x e v g t_x t =
  let gx = extend g x t_x in
  match e with
  | EVar y ->
     if x=y
     then context_invariance v empty g (* uses lemma typable_empty_closed *)
     else context_invariance e gx g

  | EApp e1 e2 ->
     substitution_preserves_typing x e1 v g;
     substitution_preserves_typing x e2 v g

  | EAbs y t_y e1 ->
     let gxy = extend gx y t_y in
     let gy = extend g y t_y in
     if x=y
     then typing_extensional gxy gy e1
     else
       (let gyx = extend gy x t_x in
        typing_extensional gxy gyx e1;
        substitution_preserves_typing x e1 v gy)

val preservation : e:exp -> t:ty{rtyping empty e t /\ is_Some (step e)} ->
      Tot (u:unit{rtyping empty (Some.v (step e)) t})
let rec preservation e t =
  match e with
  | EApp e1 e2 ->
     if is_value e1
     then (if is_value e2
           then let EAbs x _ ebody = e1 in
                substitution_preserves_typing x ebody e2 empty
           else preservation e2)
     else preservation e1

*)
