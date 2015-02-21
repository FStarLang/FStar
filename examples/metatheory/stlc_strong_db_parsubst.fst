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

module StlcStrongDbParSubst

open Constructive
open FunctionalExtensionality

(* Constructive-style progress and preservation proof for STLC with
   strong reduction, using deBruijn indices and parallel substitution. *)

type typ =
  | TArr : typ -> typ -> typ

type var = nat

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | ELam   : typ -> exp -> exp

(* Parallel substitution operation `subst` *)

(* The termination argument uses a lexicographic ordering composed of:
   0) a bit saying whether the expression is a variable or not;
   1) an _undecidable_ well-founded order on substitutions that
      equates all renamings, equates all non-renamings, and makes
      renamings strictly smaller than non-renamings; we write down a
      non-constructive function mapping substitutions (infinite
      objects) to 0 (renaming) or 1 (non-renaming)
   2) the structure of the expression e *)

type sub = var -> Tot exp

opaque type renaming (s:sub) = (forall (x:var). is_EVar (s x))

(* My proposal would be to put this in Classic not Tot *)
assume val excluded_middle : p:Type -> Tot (b:bool{b = true <==> p})

val is_renaming : s:sub -> Tot (n:int{(renaming s ==> n=0) /\
                                      (~(renaming s) ==> n=1)})
let is_renaming s = (if excluded_middle (renaming s) then 0 else 1)

val sub_inc : var -> Tot exp
let sub_inc y = EVar (y+1)

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if is_EVar e then 0 else 1

val subst : e:exp -> s:sub -> Pure exp (requires True) 
     (ensures (fun e' -> renaming s /\ is_EVar e ==> is_EVar e'))
     (decreases %[is_var e; is_renaming s; e])
let rec subst e s =
  match e with
  | EVar x -> s x

  | ELam t e1 -> 
     let subst_elam : y:var -> Tot (e:exp{renaming s ==> is_EVar e}) = fun y ->
       if y=0 
       then EVar y 
       else subst (s (y - 1)) sub_inc in
     ELam t (subst e1 subst_elam)
     
  | EApp e1 e2 -> EApp (subst e1 s) (subst e2 s)
 
val subst_elam: s:sub -> Tot sub
let subst_elam s y =
  if y = 0 then EVar y
  else subst (s (y-1)) sub_inc

val subst_extensional: s1:sub -> s2:sub{FEq s1 s2} -> e:exp ->
                       Lemma (requires True)
                             (ensures (subst e s1 = subst e s2))
                             [SMTPat (subst e s1); SMTPat (subst e s2)]
let subst_extensional s1 s2 e = ()

(* subst_beta_gen is a generalization of the substitution we do for
   the beta rule, when we've under x binders
   (useful for the substitution lemma) *)
val sub_beta_gen : var -> exp -> Tot sub
let sub_beta_gen x v = fun y -> if y < x then (EVar y)
                                      else if y = x then v
                                      else (EVar (y-1))

val subst_beta_gen : var -> exp -> exp -> Tot exp
let subst_beta_gen x v e = subst e (sub_beta_gen x v)

let subst_beta v e = subst_beta_gen 0 v e

(* Small-step operational semantics;
   non-deterministic, so necessarily in inductive form *)

type step : exp -> exp -> Type =
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp ->
            step (EApp (ELam t e1) e2) (subst_beta e2 e1)
  | SApp1 : #e1:exp ->
            e2:exp ->
            #e1':exp ->
            step e1 e1' ->
            step (EApp e1 e2) (EApp e1' e2)
  | SApp2 : e1:exp ->
            #e2:exp ->
            #e2':exp ->
            step e2 e2' ->
            step (EApp e1 e2) (EApp e1 e2')

(* Type system; in inductive form (not strictly necessary for STLC) *)

type env = var -> Tot (option typ)

val empty : env
let empty _ = None

val extend : env -> var -> typ -> Tot env
let extend g x t y = if y < x then g y 
                     else if y = x then Some t
                     else g (y-1)

type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
            x:var{is_Some (g x)} ->
              typing g (EVar x) (Some.v (g x))
  | TyLam : #g:env ->
            t:typ ->
            #e1:exp ->
            #t':typ ->
            typing (extend g 0 t) e1 t' ->
            typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:typ ->
            #t12:typ ->
            typing g e1 (TArr t11 t12) ->
            typing g e2 t11 ->
            typing g (EApp e1 e2) t12

(* Progress proof, a bit larger in constructive style *)

val is_value : exp -> Tot bool
let is_value = is_ELam

val progress : #e:exp{not (is_value e)} -> #t:typ -> h:typing empty e t ->
               Tot (cexists (fun e' -> step e e')) (decreases h)
let rec progress _ _ h =
  match h with
  | TyApp #g #e1 #e2 #t11 #t12 h1 h2 ->
     match e1 with
     | ELam t e1' -> ExIntro (subst_beta e2 e1') (SBeta t e1' e2)
     | _          -> (match progress h1 with
                      | ExIntro e1' h1' -> ExIntro (EApp e1' e2) (SApp1 e2 h1'))

(* Substitution extensional
   the proof would be trivial with the extensionality axiom *)

(* opaque logic type SubEqual (s1:sub) (s2:sub) = *)
(*                  (forall (x:var). s1 x = s2 x) *)


(* Typing extensional (weaker) and context invariance (stronger) lemmas;
   Context invariance is actually used in a single place within substitution,
   for in a specific form of weakening when typing variables. *)

val appears_free_in : x:var -> e:exp -> Tot bool (decreases e)
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | ELam _ e1 -> appears_free_in (x+1) e1

opaque logic type EnvEqualE (e:exp) (g1:env) (g2:env) =
                 (forall (x:var). appears_free_in x e ==> g1 x = g2 x)

val context_invariance : #e:exp -> #g:env -> #t:typ -> 
      h:(typing g e t) -> g':env{EnvEqualE e g g'} ->
      Tot (typing g' e t) (decreases h)
let rec context_invariance _ _ _ h g' =
  match h with
  | TyVar x -> TyVar x
  | TyLam t_y h1 ->
    TyLam t_y (context_invariance h1 (extend g' 0 t_y))
  | TyApp h1 h2 ->
    TyApp (context_invariance h1 g') (context_invariance h2 g')

(* This one would follow just by functional extensionality *)
opaque logic type EnvEqual (g1:env) (g2:env) =
                 (forall (x:var). g1 x = g2 x)

val typing_extensional : #e:exp -> #g:env -> #t:typ ->
      h:(typing g e t) -> g':env{EnvEqual g g'} ->
      Tot (typing g' e t)
let typing_extensional _ _ _ h g' = context_invariance h g'

(* Lemmas about substitution bellow lambdas and shifting *)

val sub_inc_above : nat -> var -> Tot exp
let sub_inc_above n y = if y<n then EVar y else EVar (y+1)

val shift_up_above : nat -> exp -> Tot exp
let shift_up_above n e = subst e (sub_inc_above n)

val shift_up : exp -> Tot exp
let shift_up = shift_up_above 0

val shift_up_subst_sub_inc : v:exp -> Lemma
      (ensures (shift_up v = subst v sub_inc))
let shift_up_subst_sub_inc v =
  subst_extensional (sub_inc_above 0) sub_inc v

val sub_beta_gen_elam : x:var -> v:exp -> y:var -> Lemma
      (ensures ((subst_elam (sub_beta_gen  x              v)) y =
                            (sub_beta_gen (x+1) (shift_up v)) y))
let sub_beta_gen_elam x v y =
  if y>0 && x = y-1 then shift_up_subst_sub_inc v

val subst_gen_elam_aux_forall : x:var -> v:exp -> Lemma
      (ensures (FEq (subst_elam (sub_beta_gen  x  v))
                    (sub_beta_gen (x+1) (shift_up v))))
let subst_gen_elam_aux_forall x v = ()

val subst_gen_elam : x:var -> v:exp -> t_y:typ -> e':exp -> Lemma
      (ensures (subst_beta_gen x v (ELam t_y e') =
                ELam t_y (subst_beta_gen (x+1) (shift_up v) e')))
let subst_gen_elam x v t_y e' =
  subst_gen_elam_aux_forall x v;
  subst_extensional (subst_elam (sub_beta_gen  x              v))
                                (sub_beta_gen (x+1) (shift_up v))  e'

val shift_up_above_lam : n:nat -> t:typ -> e:exp -> Lemma
  (ensures (shift_up_above n (ELam t e) = ELam t (shift_up_above (n+1) e)))
let shift_up_above_lam n t e =
  subst_extensional (subst_elam (sub_inc_above n)) (sub_inc_above (n+1)) e

(* Weakening or shifting preserves typing *)

val weakening : x:nat -> #g:env -> #e:exp -> #t:typ -> t':typ ->
      h:typing g e t -> Tot (typing (extend g x t') (shift_up_above x e) t)
      (decreases h)
let rec weakening n g v t t' h =
  match h with
  | TyVar y -> if y<n then TyVar y else TyVar (y+1)
  | TyLam #g t_y #e' #t'' h21 ->
      (shift_up_above_lam n t_y e';
       let h21 = weakening (n+1) t' h21 in
       TyLam t_y (typing_extensional h21 (extend (extend g n t') 0 t_y)))
  | TyApp h21 h22 -> TyApp (weakening n t' h21)
                           (weakening n t' h22)

(* Substitution preserves typing *)

val substitution_preserves_typing :
      x:var -> #e:exp -> #v:exp -> #t_x:typ -> #t:typ -> #g:env ->
      h1:typing g v t_x ->
      h2:typing (extend g x t_x) e t ->
      Tot (typing g (subst_beta_gen x v e) t) (decreases e)
let rec substitution_preserves_typing x e v t_x t g h1 h2 =
  match h2 with
  | TyVar y ->
     if x=y then h1
     else if y<x then context_invariance h2 g
     else             TyVar (y-1)
  | TyLam #g' t_y #e' #t' h21 ->
     (let h21' = typing_extensional h21 (extend (extend g 0 t_y) (x+1) t_x) in
      let h1' = weakening 0 t_y h1 in
      subst_gen_elam x v t_y e';
      TyLam t_y (substitution_preserves_typing (x+1) h1' h21'))
  | TyApp h21 h22 ->
    (TyApp (substitution_preserves_typing x h1 h21)
           (substitution_preserves_typing x h1 h22))

(* Type preservation *)

val preservation : #e:exp -> #e':exp -> hs:step e e' ->
                   #g:env -> #t:typ -> ht:(typing g e t) ->
                   Tot (typing g e' t) (decreases ht)
let rec preservation e e' hs g t ht =
  let TyApp #g #e1 #e2 #t11 #t12 h1 h2 = ht in
    match hs with
    | SBeta t e1' e2' -> let TyLam t_x hbody = h1 in
                         substitution_preserves_typing 0 h2 hbody
    | SApp1 e2' hs1   -> TyApp (preservation hs1 h1) h2
    | SApp2 e1' hs2   -> TyApp h1 (preservation hs2 h2)
