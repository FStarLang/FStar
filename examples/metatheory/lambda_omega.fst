(*
   Copyright 2008-2015 Catalin Hritcu, Nikhil Swamy, Microsoft Research and Inria

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

module LambdaOmega

(* Chapter 29 of TAPL: "Type Operators and Kinding" *)

type var = nat

type knd =
  | KTyp : knd
  | KArr : knd -> knd -> knd

type typ =
  | TVar : var -> typ
  | TLam : knd -> typ -> typ 
  | TApp : typ -> typ -> typ
  | TArr : typ -> typ -> typ

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | ELam   : typ -> exp -> exp

val is_value : exp -> Tot bool
let is_value = is_ELam

(* Substitution on expressions and types;
   they don't really interact in this calculus *)

(* AR: this is copied from Nik's parallel substitution termination proof *)
type esub = var -> Tot exp
type erenaming (s:esub) = (forall (x:var). is_EVar (s x))

assume val is_erenaming : s:esub -> Tot (n:int{(erenaming s ==> n=0) /\
                                               (~(erenaming s) ==> n=1)})

val esub_inc : var -> Tot exp
let esub_inc y = EVar (y+1)

val erenaming_sub_inc : unit -> Lemma (erenaming (esub_inc))
let erenaming_sub_inc _ = ()

let is_evar (e:exp) : int = if is_EVar e then 0 else 1

val esubst : e:exp -> s:esub -> Pure exp (requires True) 
                                         (ensures (fun e' -> erenaming s /\ is_EVar e ==> is_EVar e'))
                                         (decreases %[is_evar e; is_erenaming s; e])
let rec esubst e s =
  match e with
  | EVar x -> s x

  | ELam t e1 -> 
     let subst_eabs : y:var -> Tot (e:exp{erenaming s ==> is_EVar e}) = fun y ->
       if y=0 
       then EVar y 
       else (esubst (s (y - 1)) esub_inc) in
     ELam t (esubst e1 subst_eabs)
     
  | EApp e1 e2 -> EApp (esubst e1 s) (esubst e2 s)

(* type esub = var -> Tot exp *)

(* val esub_inc : var -> Tot exp *)
(* let esub_inc y = EVar (y+1) *)

(* val esubst : e:exp -> s:esub -> Tot exp *)
(* val esubst_lam : s:esub -> Tot esub *)
(* let rec esubst e s = *)
(*   match e with *)
(*   | EVar x -> s x *)
(*   | ELam t e1 -> ELam t (esubst e1 (esubst_lam s)) *)
(*   | EApp e1 e2 -> EApp (esubst e1 s) (esubst e2 s) *)
(* and esubst_lam s = *)
(*   fun y -> if y = 0 then EVar y *)
(*            else esubst (s (y-1)) esub_inc *)

(* subst_beta_gen is a generalization of the substitution we do for
   the beta rule, when we've under x binders
   (useful for the substitution lemma) *)
val esub_beta_gen : var -> exp -> Tot esub
let esub_beta_gen x e = fun y -> if y < x then (EVar y)
                                      else if y = x then e
                                      else (EVar (y-1))

val esubst_beta_gen : var -> exp -> exp -> Tot exp
let esubst_beta_gen x e' e = esubst e (esub_beta_gen x e')

let esubst_beta e' e = esubst_beta_gen 0 e' e

(* Substitution on types is very much analogous *)

type tsub = var -> Tot typ
type trenaming (s:tsub) = (forall (x:var). is_TVar (s x))

assume val is_trenaming : s:tsub -> Tot (n:int{(trenaming s ==> n=0) /\
                                               (~(trenaming s) ==> n=1)})

val tsub_inc : var -> Tot typ
let tsub_inc y = TVar (y+1)

val trenaming_sub_inc : unit -> Lemma (trenaming (tsub_inc))
let trenaming_sub_inc _ = ()

let is_tvar (t:typ) : int = if is_TVar t then 0 else 1

val tsubst : t:typ -> s:tsub -> Pure typ (requires True) 
                                         (ensures (fun t' -> trenaming s /\ is_TVar t ==> is_TVar t'))
                                         (decreases %[is_tvar t; is_trenaming s; t])
let rec tsubst t s =
  match t with
  | TVar x -> s x

  | TLam t t1 -> 
     let subst_tabs : y:var -> Tot (t:typ{trenaming s ==> is_TVar t}) = fun y ->
       if y=0 
       then TVar y 
       else (tsubst (s (y - 1)) tsub_inc) in
     TLam t (tsubst t1 subst_tabs)

  | TArr t1 t2
  | TApp t1 t2 -> TApp (tsubst t1 s) (tsubst t2 s)


(* type tsub = var -> Tot typ *)

(* val tsub_inc : var -> Tot typ *)
(* let tsub_inc y = TVar (y+1) *)

(* val tsubst : t:typ -> s:tsub -> Tot typ *)
(* val tsubst_lam : s:tsub -> Tot tsub *)
(* let rec tsubst t s = *)
(*   match t with *)
(*   | TVar x -> s x *)
(*   | TLam t t1 -> TLam t (tsubst t1 (tsubst_lam s)) *)
(*   | TApp t1 t2 -> TApp (tsubst t1 s) (tsubst t2 s) *)
(*   | TArr t1 t2 -> TArr (tsubst t1 s) (tsubst t2 s) *)
(* and tsubst_lam s = *)
(*   fun y -> if y = 0 then TVar y *)
(*            else tsubst (s (y-1)) tsub_inc *)

(* (\* ... and so is tsubst_beta *\) *)

val tsub_beta_gen : var -> typ -> Tot tsub
let tsub_beta_gen x t = fun y -> if y < x then (TVar y)
                                      else if y = x then t
                                      else (TVar (y-1))

val tsubst_beta_gen : var -> typ -> typ -> Tot typ
let tsubst_beta_gen x v e = tsubst e (tsub_beta_gen x v)

let tsubst_beta v e = tsubst_beta_gen 0 v e

(* Step relation -- going for strong reduction, just because we can *)

type step : exp -> exp -> Type =
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp ->
            step (EApp (ELam t e1) e2) (esubst_beta e2 e1)
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

(* Typing environments *)

type bnd =
  | B_x : t:typ -> bnd
  | B_a : k:knd -> bnd

val is_a : option bnd -> Tot bool
let is_a ob = is_Some ob && is_B_a (Some.v ob)

val get_knd : ob:(option bnd){is_a ob} -> Tot knd
let get_knd ob = B_a.k (Some.v ob)

val is_x : option bnd -> Tot bool
let is_x ob = is_Some ob && is_B_x (Some.v ob)

val get_typ : ob:(option bnd){is_x ob} -> Tot typ
let get_typ ob = B_x.t (Some.v ob)

type env = var -> Tot (option bnd)

val empty : env
let empty _ = None

val omap : ('a -> Tot 'b) -> option 'a -> Tot (option 'b)
let omap f o =
  match o with
  | Some a -> Some (f a)
  | None   -> None

val tmap : (typ -> Tot typ) -> bnd -> Tot bnd
let tmap f b =
  match b with
  | B_x t -> B_x (f t)
  | B_a k -> B_a k

val tsub_inc_above : nat -> var -> Tot typ
let tsub_inc_above x y = if y<x then TVar y else TVar (y+1)

val tshift_up_above : nat -> typ -> Tot typ
let tshift_up_above x t = tsubst t (tsub_inc_above x)

val tshift_up : typ -> Tot typ
let tshift_up = tshift_up_above 0

val extend : env -> var -> bnd -> Tot env
let extend g x b y = if y < x then g y
                     else if y = x then Some b
                     else omap (tmap tshift_up) (g (y-1))

(* Kinding, type equivalence, and typing rules;
   first 3 kinding and typing rules are analogous *)

type kinding : env -> typ -> knd -> Type =
  | KiVar : #g:env ->
            a:var{is_a (g a)} ->
            kinding g (TVar a) (get_knd (g a))
  | KiAbs : #g:env ->
            k:knd ->
            #t1:typ ->
            #k':knd ->
            kinding (extend g 0 (B_a k)) t1 k' ->
            kinding g (TLam k t1) (KArr k k')
  | KiApp : #g:env ->
            #t1:typ ->
            #t2:typ ->
            #k11:knd ->
            #k12:knd ->
            kinding g t1 (KArr k11 k12) ->
            kinding g t2 k11 ->
            kinding g (TApp t1 t2) k12
  | KiArr : #g:env ->
            #t1:typ ->
            #t2:typ ->
            kinding g t1 KTyp ->
            kinding g t2 KTyp ->
            kinding g (TArr t1 t2) KTyp

type tequiv : typ -> typ -> Type =
  | EqRefl : t:typ ->
             tequiv t t
  | EqSymm : #t1:typ ->
             #t2:typ ->
             tequiv t1 t2 ->
             tequiv t2 t1
  | EqTran : #t1:typ ->
             #t2:typ ->
             #t3:typ ->
             tequiv t1 t2 ->
             tequiv t2 t3 ->
             tequiv t1 t3
  | EqLam : #t :typ ->
            #t':typ ->
            k :knd ->
            tequiv t t' ->
            tequiv (TLam k t) (TLam k t')
  | EqApp : #t1 :typ ->
            #t1':typ ->
            #t2 :typ ->
            #t2':typ ->
            tequiv t1 t1' ->
            tequiv t2 t2' ->
            tequiv (TApp t1 t2) (TApp t1' t2')
  | EqBeta :k:knd ->
            t1:typ ->
            t2:typ ->
            tequiv (TApp (TLam k t1) t2) (tsubst_beta t2 t1)
  | EqArr : #t1 :typ ->
            #t1':typ ->
            #t2 :typ ->
            #t2':typ ->
            tequiv t1 t1' ->
            tequiv t2 t2' ->
            tequiv (TArr t1 t2) (TArr t1' t2')

type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
            x:var{is_x (g x)} ->
            typing g (EVar x) (get_typ (g x))
  | TyAbs : #g:env ->
            t:typ ->
            #e1:exp ->
            #t':typ ->
            kinding g t KTyp ->
            typing (extend g 0 (B_x t)) e1 t' ->
            typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:typ ->
            #t12:typ ->
            typing g e1 (TArr t11 t12) ->
            typing g e2 t11 ->
            typing g (EApp e1 e2) t12
  | TyEqu : #g:env ->
            #e:exp ->
            #t1:typ ->
            #t2:typ ->
            typing g e t1 ->
            tequiv t1 t2 ->
            kinding g t2 KTyp ->
            typing g e t2


type ex : #a:Type -> (a -> Type) -> Type =
  | ExIntro : #a:Type -> #p:(a -> Type) -> x:a -> p x -> ex p

val progress : #e:exp{not (is_value e)} -> #t:typ -> h:typing empty e t ->
               Tot (ex (fun e' -> step e e')) (decreases h)
let rec progress _ _ h =
  match h with
  | TyApp #g #e1 #e2 #t11 #t12 h1 h2 ->
    (match e1 with
      | ELam t e1' -> ExIntro (esubst_beta e2 e1') (SBeta t e1' e2)
      | _          -> (match progress h1 with
          | ExIntro e1' h1' -> ExIntro (EApp e1' e2) (SApp1 e2 h1')))

  | TyEqu h1 _ _ -> progress h1
