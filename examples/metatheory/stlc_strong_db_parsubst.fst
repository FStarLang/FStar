(*
   Copyright 2014-2015
     Simon Forest - Inria and ENS Paris
     Catalin Hritcu - Inria
     Nikhil Swamy - Microsoft Research

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
open Classical
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
      non-constructive function is_renaming mapping substitutions
      (infinite objects) to 0 (renaming) or 1 (non-renaming)
   2) the structure of the expression e *)

type sub = var -> Tot exp

type renaming (s:sub) = (forall (x:var). is_EVar (s x))

val is_renaming : s:sub -> GTot (n:int{  (renaming s  ==> n=0) /\
                                       (~(renaming s) ==> n=1)})
let is_renaming s = (if excluded_middle (renaming s) then 0 else 1)

val sub_inc : var -> Tot exp
let sub_inc y = EVar (y+1)

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if is_EVar e then 0 else 1

val subst : s:sub -> e:exp -> Pure exp (requires True)
     (ensures (fun e' -> (renaming s /\ is_EVar e) ==> is_EVar e'))
     (decreases %[is_var e; is_renaming s; e])
let rec subst s e =
  match e with
  | EVar x -> s x

  | ELam t e1 ->
     let sub_elam : y:var -> Tot (e:exp{renaming s ==> is_EVar e}) =
       fun y -> if y=0 then EVar y
                       else subst sub_inc (s (y-1))            (* shift +1 *)
     in ELam t (subst sub_elam e1)

  | EApp e1 e2 -> EApp (subst s e1) (subst s e2)

val sub_elam: s:sub -> Tot sub
let sub_elam s y = if y=0 then EVar y
                   else subst sub_inc (s (y-1))

val sub_beta : exp -> Tot sub
let sub_beta v = fun y -> if y = 0 then v      (* substitute *)
                          else (EVar (y-1))    (* shift -1 *)

(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily as inductive relation *)

type step : exp -> exp -> Type =
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp ->
            step (EApp (ELam t e1) e2) (subst (sub_beta e2) e1)
  | SApp1 : #e1:exp ->
             e2:exp ->
            #e1':exp ->
            =hst:step e1 e1' ->
                 step (EApp e1 e2) (EApp e1' e2)
  | SApp2 :  e1:exp ->
            #e2:exp ->
            #e2':exp ->
            =hst:step e2 e2' ->
                 step (EApp e1 e2) (EApp e1 e2')

(* Type system; as inductive relation (not strictly necessary for STLC) *)

type env = var -> Tot (option typ)

val empty : env
let empty _ = None

(* we only need extend at 0 *)
val extend : typ -> env -> Tot env
let extend t g y = if y = 0 then Some t
                   else g (y-1)

type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
             x:var{is_Some (g x)} ->
             typing g (EVar x) (Some.v (g x))
  | TyLam : #g :env ->
             t :typ ->
            #e1:exp ->
            #t':typ ->
            =hbody:typing (extend t g) e1 t' ->
                   typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:typ ->
            #t12:typ ->
            =h1:typing g e1 (TArr t11 t12) ->
            =h2:typing g e2 t11 ->
                typing g (EApp e1 e2) t12

(* Progress *)

val is_value : exp -> Tot bool
let is_value = is_ELam

opaque val progress : #e:exp -> #t:typ -> h:typing empty e t ->
                         Pure (cexists (fun e' -> step e e'))
                              (requires (not (is_value e)))
                              (ensures (fun _ -> True)) (decreases h)
let rec progress _ _ h =
  match h with
  | TyApp #g #e1 #e2 #t11 #t12 h1 h2 ->
     match e1 with
     | ELam t e1' -> ExIntro (subst (sub_beta e2) e1') (SBeta t e1' e2)
     | _          -> let ExIntro e1' h1' = progress h1 in
                     ExIntro (EApp e1' e2) (SApp1 e2 h1')

(* Substitution extensional - used by substitution lemma below *)
val subst_extensional: s1:sub -> s2:sub{FEq s1 s2} -> e:exp ->
                       Lemma (requires True)
                             (ensures (subst s1 e = subst s2 e))
                             [SMTPat (subst s1 e); SMTPat (subst s2 e)]
let subst_extensional s1 s2 e = ()

(* Typing of substitutions (very easy, actually) *)
type subst_typing (s:sub) (g1:env) (g2:env) =
  (x:var{is_Some (g1 x)} -> Tot(typing g2 (s x) (Some.v (g1 x))))

(* Substitution preserves typing
   Strongest possible statement; suggested by Steven Schäfer *)
opaque val substitution :
      #g1:env -> #e:exp -> #t:typ -> s:sub -> #g2:env ->
      h1:typing g1 e t ->
      hs:subst_typing s g1 g2 ->
      Tot (typing g2 (subst s e) t)
      (decreases %[is_var e; is_renaming s; e])
let rec substitution g1 e t s g2 h1 hs =
  match h1 with
  | TyVar x -> hs x
  | TyApp hfun harg -> TyApp (substitution s hfun hs) (substitution s harg hs)
  | TyLam tlam hbody ->
     let hs'' : subst_typing (sub_inc) g2 (extend tlam g2) =
       fun x -> TyVar (x+1) in
     let hs' : subst_typing (sub_elam s) (extend tlam g1) (extend tlam g2) =
       fun y -> if y = 0 then TyVar y
                else substitution sub_inc (hs (y - 1)) hs''
     in TyLam tlam (substitution (sub_elam s) hbody hs')

(* Weakening (or shifting preserves typing) *)
(* Useless now, showing that it follows from substitution lemma *)
val sub_inc_above : nat -> var -> Tot exp
let sub_inc_above n y = if y<n then EVar y else EVar (y+1)

val shift_up_above : nat -> exp -> Tot exp
let shift_up_above n e = subst (sub_inc_above n) e

val extend_gen : var -> typ -> env -> Tot env
let extend_gen x t g y = if y < x then g y
                         else if y = x then Some t
                         else g (y-1)

opaque val weakening : n:nat -> #g:env -> #e:exp -> #t:typ -> t':typ ->
      h:typing g e t -> Tot (typing (extend_gen n t' g) (shift_up_above n e) t)
      (decreases h)
let rec weakening n g v t t' h =
  let hs : subst_typing (sub_inc_above n) g (extend_gen n t' g) =
    fun y -> if y < n then TyVar y else TyVar (y+1)
  in substitution (sub_inc_above n) h hs

(* Substitution for beta reduction
   Now just a special case of substitution lemma *)
opaque val substitution_beta :
      #e:exp -> #v:exp -> #t_x:typ -> #t:typ -> #g:env ->
      h1:typing g v t_x ->
      h2:typing (extend t_x g) e t ->
      Tot (typing g (subst (sub_beta v) e) t) (decreases e)
let rec substitution_beta e v t_x t g h1 h2 =
  let hs : subst_typing (sub_beta v) (extend t_x g) g =
    fun y -> if y = 0 then h1 else TyVar (y-1) in
  substitution (sub_beta v) h2 hs

(* Type preservation *)
opaque val preservation : #e:exp -> #e':exp -> hs:step e e' ->
                          #g:env -> #t:typ -> ht:(typing g e t) ->
                          Tot (typing g e' t) (decreases ht)
let rec preservation e e' hs g t ht =
  let TyApp h1 h2 = ht in
  match hs with
  | SBeta t e1' e2' -> substitution_beta h2 (TyLam.hbody h1)
  | SApp1 e2' hs1   -> TyApp (preservation hs1 h1) h2
  | SApp2 e1' hs2   -> TyApp h1 (preservation hs2 h2)
