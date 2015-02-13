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

module StlcConstrDeBruijn

type ty =
  | TArrow : t1:ty -> t2:ty -> ty

type var = nat

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : ty -> exp -> exp

val is_value : exp -> Tot bool
let is_value = is_EAbs

type sub = var -> Tot exp

(* Parallel substitution operation *)
val subst : e:exp -> sub -> Tot exp (decreases e)
let rec subst e s =
  match e with
  | EVar x -> s x
  | EAbs t e1 -> EAbs t (subst e1 (fun x -> if x = 0 then EVar x else s (x+1)))
  | EApp e1 e2 -> EApp (subst e1 s) (subst e2 s)

val subst_beta : exp -> exp -> Tot exp
let subst_beta v e =
  subst e (fun x -> if x = 0 then v else EVar (x-1))

val step : exp -> Tot (option exp)
let rec step e =
  match e with
  | EApp e1 e2 ->
      if is_value e1 then
        if is_value e2 then
          match e1 with
          | EAbs t e' -> Some (subst_beta e' e2)
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

val extend : env -> ty -> Tot env
let extend g t x = if x = 0 then Some t else g (x-1)

type rtyping : env -> exp -> ty -> Type =
  | TyVar : #g:env ->
            x:var{is_Some (g x)} ->
              rtyping g (EVar x) (Some.v (g x))
  | TyAbs : #g:env ->
            t:ty ->
            #e1:exp ->
            #t':ty ->
            rtyping (extend g t) e1 t' ->
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
      Lemma (ensures (is_value e \/ (is_Some (step e)))) (decreases h)
let rec progress _ _ h =
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
      Lemma (ensures (appears_free_in x e ==> is_Some (g x))) (decreases h)
let rec free_in_context x _ _ _ h =
  match h with
  | TyVar x -> ()
  | TyAbs t h1 -> free_in_context (x+1) h1
  | TyApp h1 h2 -> free_in_context x h1; free_in_context x h2

val typable_empty_closed : x:var -> #e:exp -> #t:ty -> rtyping empty e t ->
      Lemma (ensures (not(appears_free_in x e)))
(*      [SMTPat (appears_free_in x e)] -- CH: adding this makes it fail! *)
let typable_empty_closed x _ _ h = free_in_context x h

val typable_empty_closed' : #e:exp -> #t:ty -> rtyping empty e t ->
      Lemma (ensures (forall (x:var). (not(appears_free_in x e))))
let typable_empty_closed' _ _ h = admit() (* CH: need forall_intro for showing this *)

opaque logic type Equal (g1:env) (g2:env) =
                 (forall (x:var). g1 x=g2 x)
opaque logic type EqualE (e:exp) (g1:env) (g2:env) =
                 (forall (x:var). appears_free_in x e ==> g1 x=g2 x)

val context_invariance : #e:exp -> #g:env -> #t:ty -> 
      h:(rtyping g e t) -> g':env{EqualE e g g'} ->
      Tot (rtyping g' e t) (decreases h)
let rec context_invariance _ _ _ h g' =
  match h with
  | TyVar x -> TyVar x
  | TyAbs t_y h1 ->
    TyAbs t_y (context_invariance h1 (extend g' t_y))
  | TyApp h1 h2 ->
    TyApp (context_invariance h1 g') (context_invariance h2 g')

val typing_extensional : #e:exp -> #g:env -> #t:ty ->
      h:(rtyping g e t) -> g':env{Equal g g'} ->
      Tot (rtyping g' e t)
let typing_extensional _ _ _ h g' = context_invariance h g'

assume val admit: unit -> Pure 'a (requires True) (ensures (fun _ -> False))

val subst_gen : var -> exp -> exp -> Tot exp
let subst_gen x v e =
  subst e (fun y -> if y < x then (EVar y)
                    else if y = x then v
                    else (EVar (y-1+x)))

(* Proof of this will probably rely on an extensionality property of subst *)
val subst_beta_gen : v:exp -> e:exp -> Lemma 
  (ensures (subst_beta v e = subst_gen 0 v e)) (decreases e)
let subst_beta_gen v e =
  match e with
  | EVar _ -> admit()
  | EAbs _ _ -> admit()
  | EApp _ _  -> admit()

val subst_gen_var_eq : x:var -> v:exp -> Lemma
  (ensures (subst_gen x v (EVar x) = v))
let subst_gen_var_eq x v = admit()

val subst_gen_var_neq : x:var -> y:var -> v:exp -> Lemma
  (ensures (subst_gen x v (EVar y) = (EVar y)))
let subst_gen_var_neq x y v = admit()

val extend_gen : var -> env -> ty -> Tot env
let extend_gen x g t y = if y < x then g y 
                         else if y = x then Some t
                         else g (y-1)

val substitution_preserves_typing :
      x:var -> #e:exp -> #v:exp -> #t_x:ty -> #t:ty -> #g:env ->
      h1:rtyping empty v t_x ->
      h2:rtyping (extend_gen x g t_x) e t ->
      Tot (rtyping g (subst_gen x v e) t) (decreases e)
let rec substitution_preserves_typing x e v t_x t g h1 h2 =
  match h2 with
  | TyVar y ->
     if x=y
     then (typable_empty_closed' h1;
           subst_gen_var_eq x v;
           context_invariance h1 g)
     else (subst_gen_var_neq x y v;
           (*assert(EqualE e (extend_gen x g t_x) g);
             -- this assert fails, so we can't call context_invariance *)
           admit() (*context_invariance h2 g*))
  | TyAbs t_y h21 -> admit()
(*
     let gy = extend g t_y in
     if x=0
     then TyAbs t_y (typing_extensional h21 gy)
     else
       (let h21' = typing_extensional h21 (extend gy t_x) in
        TyAbs t_y (substitution_preserves_typing x h1 h21'))
*)
  | TyApp #g' #e1 #e2 #t11 #t12 h21 h22 -> admit()
(*
     (* CH: implicits don't work here, why? *)
     TyApp #g #(subst_gen x v e1) #(subst_gen x v e2) #t11 #t12
       (substitution_preserves_typing x h1 h21)
       (substitution_preserves_typing x h1 h22)
*)

assume val subst_beta_preserves_typing :
      #e:exp -> #v:exp -> #t_x:ty -> #t:ty -> #g:env ->
      h1:rtyping empty v t_x ->
      h2:rtyping (extend g t_x) e t ->
      Tot (rtyping g (subst_beta v e) t) (decreases e)

(*
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
*)
