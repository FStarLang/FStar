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

module StlcCbvDbParSubst

(* Constructive style progress and preservation proof for STLC with
   CBV reduction, using deBruijn indices and parallel substitution.
   An awkward special case of stlc_strong...; in fact this proof
   is _more_ complex than the one in stlc_strong...! *)

open StlcStrongDbParSubst
open FunctionalExtensionality

val step : exp -> Tot (option exp)
let rec step e =
  match e with
  | EApp e1 e2 ->
      if is_value e1 then
        if is_value e2 then
          match e1 with
          | ELam t e' -> Some (subst_beta e2 e')
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

val progress : #e:exp -> #t:typ -> h:typing empty e t ->
      Lemma (ensures (is_value e \/ (is_Some (step e)))) (decreases h)
let rec progress _ _ h =
  match h with
  | TyVar _   -> ()
  | TyLam _ _ -> ()
  | TyApp h1 h2 -> progress h1; progress h2

(* Typing extensional (weaker) and context invariance (stronger) lemmas *)

(* Typing extensional follows directly from functional extensionality
   (it's also a special case of context invariance below) *)

opaque val typing_extensional : #e:exp -> #g:env -> #t:typ ->
      h:(typing g e t) -> g':env{FEq g g'} -> Tot (typing g' e t)
let typing_extensional _ _ _ h _ = h

val appears_free_in : x:var -> e:exp -> Tot bool (decreases e)
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | ELam _ e1 -> appears_free_in (x+1) e1

opaque logic type EnvEqualE (e:exp) (g1:env) (g2:env) =
                 (forall (x:var). appears_free_in x e ==> g1 x = g2 x)

(* Context invariance (actually used in a single place within substitution,
   for in a specific form of weakening when typing variables) *)
opaque val context_invariance : #e:exp -> #g:env -> #t:typ ->
      h:(typing g e t) -> g':env{EnvEqualE e g g'} ->
      Tot (typing g' e t) (decreases h)
let rec context_invariance _ _ _ h g' =
  match h with
  | TyVar x -> TyVar x
  | TyLam t_y h1 ->
    TyLam t_y (context_invariance h1 (extend g' 0 t_y))
  | TyApp h1 h2 ->
    TyApp (context_invariance h1 g') (context_invariance h2 g')

val free_in_context : x:var -> #e:exp -> #g:env -> #t:typ -> h:typing g e t ->
      Lemma (ensures (appears_free_in x e ==> is_Some (g x))) (decreases h)
let rec free_in_context x _ _ _ h =
  match h with
  | TyVar x -> ()
  | TyLam t h1 -> free_in_context (x+1) h1
  | TyApp h1 h2 -> free_in_context x h1; free_in_context x h2

val typable_empty_not_free : x:var -> #e:exp -> #t:typ -> typing empty e t ->
      Lemma (ensures (not (appears_free_in x e)))
(*      [SMTPat (appears_free_in x e)] -- CH: adding this makes it fail! *)
let typable_empty_not_free x _ _ h = free_in_context x h

val below : x:var -> e:exp -> Tot bool (decreases e)
let rec below x e =
  match e with
  | EVar y -> y < x
  | EApp e1 e2 -> below x e1 && below x e2
  | ELam _ e1 -> below (x+1) e1

val closed : exp -> Tot bool
let closed = below 0

(* at some point we could try again to relate closed and appears_free *)
(* this didn't work for some reason
  forall_intro #var #(fun (x:var) -> not (appears_free_in x e))
    (fun (x:var) -> typable_empty_closed x h)
*)
type pclosed (e:exp) = (forall (x:var). not (appears_free_in x e))
assume val closed_appears_free : e:exp{closed e} -> Lemma (ensures (pclosed e))
assume val appears_free_closed : e:exp{pclosed e} -> Lemma (ensures (closed e))
(*
let rec appears_free_closed e =
  match e with
  | EVar _ -> ()
  | EApp e1 e2 -> appears_free_closed e1; appears_free_closed e2
  | ELam _ e1 -> appears_free_closed e1
*)

type below_env (x:var) (g:env) = (forall (y:var). y >= x ==> g y = None)

val typable_below : x:var -> #g:env{below_env x g} -> #e:exp -> #t:typ
                          -> h:typing g e t ->
      Lemma (ensures (below x e)) (decreases h)
let rec typable_below x g _ _ h =
  match h with
  | TyVar y -> ()
  | TyApp h1 h2 -> typable_below x h1; typable_below x h2
  | TyLam _y h1 -> typable_below (x+1) h1

val typable_empty_closed : #e:exp -> #t:typ -> h:typing empty e t ->
      Lemma (ensures (closed e))
let typable_empty_closed e t h = typable_below 0 h



val subst_gen_var_lt : x:var -> y:var{y < x} -> v:exp -> Lemma
  (ensures (subst_beta_gen x v (EVar y) = (EVar y)))
let subst_gen_var_lt x y v = ()

val extend_lt : x:var -> y:var{y < x} -> g:env -> t_x:typ -> Lemma
     (ensures (extend g x t_x) y = g y)
let extend_lt x y g t_x = ()

val extend_gt : x:var -> y:var{y > x} -> g:env -> t_x:typ -> Lemma
     (ensures (extend g x t_x) y = g (y-1))
let extend_gt x y g t_x = ()

val extend_twice : x:var -> g:env -> t_x:typ -> t_y:typ -> Lemma
      (ensures (FEq (extend (extend g x t_x) 0     t_y)
                      (extend (extend g 0 t_y) (x+1) t_x)))
let extend_twice x g t_x t_y = ()

type sub_below (x:var) (s:sub) = (forall (y:var). y<x ==> s y = EVar y)

val subst_below : x:var -> v:exp{below x v} -> s:sub{sub_below x s} ->
  Lemma (ensures (v = subst s v)) (decreases v)
let rec subst_below x v s =
  match v with
  | EVar y     -> ()
  | EApp e1 e2 -> subst_below x e1 s; subst_below x e2 s
  | ELam t e   -> (subst_below (x+1) e (subst_elam s);
                   assert(e = subst (subst_elam s) e);
                   assert(v = ELam t e);
                   assert(subst s v = ELam t (subst (subst_elam s) e)))

val subst_closed : v:exp{closed v} -> s:sub ->
  Lemma (ensures (v = subst s v)) (decreases v)
let rec subst_closed v s = subst_below 0 v s

val subst_gen_elam_aux : x:var -> v:exp{closed v} -> y:var -> Lemma
      (ensures ((subst_elam (sub_beta_gen  x    v)) y =
                            (sub_beta_gen (x+1) v)  y))
let subst_gen_elam_aux x v y =
  if y = 0 then ()
  else
    (assert((subst_elam (sub_beta_gen x v)) y =
           (subst sub_inc (sub_beta_gen x v (y-1))));
          if y-1 < x then ()
     else if y-1 = x then
            (assert(sub_beta_gen x v (y-1) = v);
             assert(sub_beta_gen (x+1) v y = v);
             subst_closed v sub_inc)
     else ())

val subst_gen_elam_aux_forall : x:var -> v:exp{closed v} -> Lemma
      (ensures (FEq (subst_elam (sub_beta_gen  x    v))
                                (sub_beta_gen (x+1) v)))
let subst_gen_elam_aux_forall x v = admit()
(* should follow from subst_gen_elam_aux and forall_intro *)

val subst_gen_elam : x:var -> v:exp{closed v} -> t_y:typ -> e':exp -> Lemma
      (ensures (subst_beta_gen x v (ELam t_y e') =
                ELam t_y (subst_beta_gen (x+1) v e')))
let subst_gen_elam x v t_y e' =
  subst_gen_elam_aux_forall x v;
  subst_extensional (subst_elam (sub_beta_gen  x    v))
                                      (sub_beta_gen (x+1) v)  e';
  assert(subst_beta_gen x v (ELam t_y e')
           = ELam t_y (subst (subst_elam (sub_beta_gen x v)) e'))

val substitution_preserves_typing :
      x:var -> #e:exp -> #v:exp -> #t_x:typ -> #t:typ -> #g:env ->
      h1:typing empty v t_x ->
      h2:typing (extend g x t_x) e t ->
      Tot (typing g (subst_beta_gen x v e) t) (decreases e)
let rec substitution_preserves_typing x e v t_x t g h1 h2 =
  match h2 with
  | TyVar y ->
     if x=y then      (typable_empty_closed h1;
                       closed_appears_free v;
                       context_invariance h1 g)
     else if y<x then context_invariance h2 g
     else             TyVar (y-1)
  | TyLam #g' t_y #e' #t' h21 ->
     (let h21' = typing_extensional h21 (extend (extend g 0 t_y) (x+1) t_x) in
      typable_empty_closed h1;
      subst_gen_elam x v t_y e';
      TyLam t_y (substitution_preserves_typing (x+1) h1 h21'))
  | TyApp #g' #e1 #e2 #t11 #t12 h21 h22 ->
     (* CH: implicits don't work here, why? *)
    (TyApp #g #(subst_beta_gen x v e1) #(subst_beta_gen x v e2) #t11 #t12
       (substitution_preserves_typing x h1 h21)
       (substitution_preserves_typing x h1 h22))

val preservation : #e:exp{is_Some (step e)} -> #t:typ -> h:(typing empty e t) ->
      Tot (typing empty (Some.v (step e)) t) (decreases e)
let rec preservation e t h =
  let TyApp #g #e1 #e2 #t11 #t12 h1 h2 = h in
     if is_value e1
     then (if is_value e2
           then let TyLam t_x hbody = h1 in
                substitution_preserves_typing 0 h2 hbody
           else TyApp h1 (preservation h2))
     else TyApp (preservation h1) h2
