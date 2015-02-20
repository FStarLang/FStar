(*
   Copyright 2008-2015 Catalin Hritcu (Inria), Aseem Rastogi (UMD), and
   Nikhil Swamy (Microsoft Research)
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

open FunctionalExtensionality

(* Chapter 29 of TAPL: "Type Operators and Kinding",
   proof follows Chapter 30, but we don't consider polymorphism *)

type var = nat

type knd =
  | KTyp : knd
  | KArr : knd -> knd -> knd

type typ =
  | TVar : var -> typ
  | TLam : knd -> t:typ -> typ 
  | TApp : typ -> typ -> typ
  | TArr : typ -> typ -> typ

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | ELam   : typ -> exp -> exp

(* Substitution on expressions and types;
   they don't really interact in this calculus *)

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
     let subst_elam : y:var -> Tot (e:exp{erenaming s ==> is_EVar e}) = fun y ->
       if y=0 then EVar y
       else (esubst (s (y - 1)) esub_inc) in
     ELam t (esubst e1 subst_elam)
     
  | EApp e1 e2 -> EApp (esubst e1 s) (esubst e2 s)

val esubst_lam: s:esub -> Tot esub
let esubst_lam s y =
  if y = 0 then EVar y
  else esubst (s (y-1)) esub_inc

(* Substitution extensional; trivial with the extensionality axiom *)
val esubst_extensional: s1:esub -> s2:esub{FEq s1 s2} -> e:exp ->
                       Lemma (requires True) (ensures (esubst e s1 = esubst e s2))
(*                       [SMTPat (esubst e s1);  SMTPat (esubst e s2)]*)
let esubst_extensional s1 s2 e = ()

(* This only works with the patterns in subst_extensional above;
   it would be a lot cooler if this worked without, since it increases checking time
val esubst_lam_hoist : t:typ -> e:exp -> s:esub -> Lemma
      (ensures (esubst (ELam t e) s = ELam t (esubst e (esubst_lam s))))
let esubst_lam_hoist t e s = ()
*)

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

  | TLam k t1 -> 
     let tsubst_lam : y:var -> Tot (t:typ{trenaming s ==> is_TVar t}) = fun y ->
       if y=0 
       then TVar y 
       else (tsubst (s (y - 1)) tsub_inc) in
     TLam k (tsubst t1 tsubst_lam)

  | TArr t1 t2 -> TArr (tsubst t1 s) (tsubst t2 s)
  | TApp t1 t2 -> TApp (tsubst t1 s) (tsubst t2 s)

val tsubst_lam: s:tsub -> Tot tsub
let tsubst_lam s y =
  if y = 0 then TVar y
  else tsubst (s (y-1)) tsub_inc

(* Type substitution extensional; trivial with the extensionality axiom *)
val tsubst_extensional: s1:tsub -> s2:tsub{FEq s1 s2} -> t:typ ->
                       Lemma (requires True) (ensures (tsubst t s1 = tsubst t s2))
(*                       [SMTPat (tsubst t s1);  SMTPat (tsubst t s2)]*)
let tsubst_extensional s1 s2 t = ()

(* This only works with the patterns in tsubst_extensional above;
   it would be a lot cooler if this worked without, since it increases checking time
val tsubst_lam_hoist : k:knd -> t:typ -> s:tsub -> Lemma
      (ensures (tsubst (TLam k t) s = TLam k (tsubst t (tsubst_lam s))))
let tsubst_lam_hoist k t s = ()
*)

val tsub_beta_gen : var -> typ -> Tot tsub
let tsub_beta_gen x t = fun y -> if y < x then (TVar y)
                                 else if y = x then t
                                 else (TVar (y-1))

val tsubst_beta_gen : var -> typ -> typ -> Tot typ
let tsubst_beta_gen x t' t = tsubst t (tsub_beta_gen x t')

let tsubst_beta t' t = tsubst_beta_gen 0 t' t

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

type a_env = nat -> Tot (option knd)
type x_env = nat -> Tot (option typ)

val empty_a: a_env
let empty_a = fun _ -> None

val empty_x: x_env
let empty_x = fun _ -> None

type env =
  | MkEnv: a:a_env -> x:x_env -> env

val lookup_tvar: env -> nat -> Tot (option knd)
let lookup_tvar g n = MkEnv.a g n

val lookup_evar: env -> nat -> Tot (option typ)
let lookup_evar g n = MkEnv.x g n

val empty: env
let empty = MkEnv empty_a empty_x

val tsub_inc_above : nat -> var -> Tot typ
let tsub_inc_above x y = if y<x then TVar y else TVar (y+1)

val tshift_up_above : nat -> typ -> Tot typ
let tshift_up_above x t = tsubst t (tsub_inc_above x)

val tshift_up : typ -> Tot typ
let tshift_up = tshift_up_above 0

val extend_tvar: g:env -> n:nat -> k:knd -> Tot env
let extend_tvar g n k =
  let a_env = fun a -> if a < n then lookup_tvar g a
                       else if a = n then Some k
                       else lookup_tvar g (a - 1) in
  let x_env = fun x -> match lookup_evar g x with
    | None -> None
    | Some t -> Some (tshift_up_above n t)
  in
  MkEnv a_env x_env

val extend_evar: g:env -> n:nat -> t:typ -> Tot env
let extend_evar g n t =
  let a_env = fun a -> lookup_tvar g a in
  let x_env = fun x -> if x < n then lookup_evar g x
                       else if x = n then Some t
                       else lookup_evar g (x - 1) in
  MkEnv a_env x_env

(* Kinding, type equivalence, and typing rules;
   first 3 kinding and typing rules are analogous *)

type kinding : env -> typ -> knd -> Type =
  | KiVar : #g:env ->
            a:var{is_Some (lookup_tvar g a)} ->
            kinding g (TVar a) (Some.v (lookup_tvar g a))
  | KiLam : #g:env ->
            k:knd ->
            #t:typ ->
            #k':knd ->
            kinding (extend_tvar g 0 k) t k' ->
            kinding g (TLam k t) (KArr k k')
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
            x:var{is_Some (lookup_evar g x)} ->
            typing g (EVar x) (Some.v (lookup_evar g x))
  | TyLam : #g:env ->
            t:typ ->
            #e1:exp ->
            #t':typ ->
            kinding g t KTyp ->
            typing (extend_evar g 0 t) e1 t' ->
            typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t1:typ ->
            #t2:typ ->
            typing g e1 (TArr t1 t2) ->
            typing g e2 t1 ->
            typing g (EApp e1 e2) t2
  | TyEqu : #g:env ->
            #e:exp ->
            #t1:typ ->
            #t2:typ ->
            typing g e t1 ->
            tequiv t1 t2 ->
            kinding g t2 KTyp ->
            typing g e t2

(* Progress proof *)

type ex : #a:Type -> (a -> Type) -> Type =
  | ExIntro : #a:Type -> #p:(a -> Type) -> x:a -> p x -> ex p

val is_value : exp -> Tot bool
let is_value = is_ELam

val progress : #e:exp{not (is_value e)} -> #t:typ -> h:typing empty e t ->
               Tot (ex (fun e' -> step e e')) (decreases h)
let rec progress _ _ h = admit()
(* takes 1s to check
  match h with
    | TyApp #g #e1 #e2 #t11 #t12 h1 h2 ->
      (match e1 with
       | ELam t e1' -> ExIntro (esubst_beta e2 e1') (SBeta t e1' e2)
       | _ -> (match progress h1 with
                | ExIntro e1' h1' -> ExIntro (EApp e1' e2) (SApp1 e2 h1')))
    | TyEqu h1 _ _ -> progress h1
*)

val tappears_free_in : x:var -> t:typ -> Tot bool (decreases t)
let rec tappears_free_in x t =
  match t with
  | TVar y -> x = y
  | TArr t1 t2
  | TApp t1 t2 -> tappears_free_in x t1 || tappears_free_in x t2
  | TLam _ t1 -> tappears_free_in (x+1) t1

opaque logic type EnvEqualT (t:typ) (g1:env) (g2:env) =
		 (forall (x:var). tappears_free_in x t ==>
                    lookup_tvar g1 x = lookup_tvar g2 x)

val tcontext_invariance : #t:typ -> #g:env -> #k:knd ->
                          h:(kinding g t k) -> g':env{EnvEqualT t g g'} ->
                          Tot (kinding g' t k) (decreases h)
let rec tcontext_invariance _ _ _ h g' = admit()
(* this takes ~5s to check
  match h with
  | KiVar a -> KiVar a
  | KiLam k1 h1 -> KiLam k1 (tcontext_invariance h1 (extend_tvar g' 0 k1))
  | KiApp h1 h2 -> KiApp (tcontext_invariance h1 g') (tcontext_invariance h2 g')
  | KiArr h1 h2 -> KiArr (tcontext_invariance h1 g') (tcontext_invariance h2 g')
*)

(* Defining constructive if-and-only-if *)
type cand : Type -> Type -> Type =
  | Conj : #a:Type -> #b:Type -> pa:a -> pb:b -> cand a b
type ciff (a : Type) (b : Type) = cand (a -> Tot b) (b -> Tot a)

val id : 'a -> Tot 'a
let id x = x

val fcomp : ('a -> Tot 'b) -> ('b -> Tot 'c) -> 'a -> Tot 'c
let fcomp f1 f2 a = f2 (f1 a)

val kinding_tequiv : #g:env -> #t1:typ -> #t2:typ -> #k:knd -> h:(tequiv t1 t2) ->
      Tot (ciff (kinding g t1 k) (kinding g t2 k)) (decreases h)
let rec kinding_tequiv g _ _ k h =
  match h with
  | EqRefl t -> Conj id id
  | EqSymm h ->
     let Conj ih1 ih2 = kinding_tequiv h in Conj ih2 ih1
  | EqTran #t1 #t2 #t3 h1 h2 ->
     let Conj ih11 ih12 = kinding_tequiv h1 in
     let Conj ih21 ih22 = kinding_tequiv h2 in
     Conj #(kinding g t1 k -> Tot (kinding g t3 k))
          #(kinding g t3 k -> Tot (kinding g t1 k))
          (fcomp ih11 ih21) (fcomp ih22 ih12)
(* This should work
     Conj (fcomp ih11 ih21) (fcomp ih22 ih12)
but instead we get this subtyping error for the second conjunct:
Subtyping check failed;
expected type ((kinding _1019 _1023  _1025) -> Tot (kinding _1019 _1021  _1025));
     got type ((kinding _1019 _33555 _1025) -> Tot (kinding _1019 _33555 _1025))
(lambda_omega.fst(372,28-372,45))
   Seems like the same kind of problem as #129 *)
  | _ -> admit ()

val eappears_free_in : x:var -> e:exp -> Tot bool (decreases e)
let rec eappears_free_in x e =
  match e with
    | EVar y -> x = y
    | EApp e1 e2 -> eappears_free_in x e1 || eappears_free_in x e2
    | ELam _ e1 -> eappears_free_in (x+1) e1

(* g1 and g2 are same for type variables,
   but they can vary on the unused term variables *)
opaque logic type EnvEqualE (e:exp) (g1:env) (g2:env) =
		 (forall (x:var). eappears_free_in x e ==>
                    lookup_evar g1 x = lookup_evar g2 x) /\
		 (FEq (MkEnv.a g1) (MkEnv.a g2))

(* g |- t :: k, g and g' are same for type variables, then g' |- t :: k *)
(* CH: this is a form of "kinding_extensional";
       it doesn't directly follow from functional extensionality,
       because (MkEnv.x g) and (MkEnv.x g') are completely unrelated;
       this is just because we pass this useless argument to kinding. *)
val kinding_extensional: #g:env -> #t:typ -> #k:knd -> h:(kinding g t k) ->
                g':env{FEq (MkEnv.a g) (MkEnv.a g')} ->
                Tot (kinding g' t k) (decreases h)
let rec kinding_extensional _ _ _ h g' =
  match h with
    | KiVar a -> KiVar a
    | KiLam k1 h1 -> KiLam k1 (kinding_extensional h1 (extend_tvar g' 0 k1))
    | KiApp h1 h2 -> KiApp (kinding_extensional h1 g') (kinding_extensional h2 g')
    | KiArr h1 h2 -> KiArr (kinding_extensional h1 g') (kinding_extensional h2 g')

val econtext_invariance : #e:exp -> #g:env -> #t:typ ->
      h:(typing g e t) -> g':env{EnvEqualE e g g'} ->
      Tot (typing g' e t) (decreases h)
let rec econtext_invariance _ _ t h g' =
  match h with
    | TyVar x -> TyVar x
    | TyLam #g t_y #e1 #t' hk h1 ->
      TyLam t_y (tcontext_invariance hk g')
  	(econtext_invariance #e1 #(extend_evar g 0 t_y) #t' h1
  	   (extend_evar g' 0 t_y))
    | TyApp h1 h2 -> TyApp (econtext_invariance h1 g')
                           (econtext_invariance h2 g')
    | TyEqu h1 eq k -> TyEqu (econtext_invariance h1 g') eq (kinding_extensional k g')

(* kinding weakening when a term variable binding is added to env *)
val kinding_weakening_ebnd : #g:env -> #t:typ -> #k:knd ->
      h:(kinding g t k) -> x:var -> t':typ ->
      Tot (kinding (extend_evar g x t') t k)
let kinding_weakening_ebnd g t k h x t' = kinding_extensional h (extend_evar g x t')

(* AR: TODO, limitation *)
val tshift_up_above_lam: n:nat -> k:knd -> t:typ -> Lemma
  (ensures (tshift_up_above n (TLam k t) = TLam k (tshift_up_above (n + 1) t)))
let tshift_up_above_lam n k t =
  assert(tshift_up_above n (TLam k t) = tsubst (TLam k t) (tsub_inc_above n));
(*  assert(tshift_up_above n (TLam k t) = TLam k (tsubst t (tsubst_lam (tsub_inc_above n)))); -- indeed, this seems like the same hoisting that Nik proved in psub.fst *)
  admit()

val esub_inc_above : nat -> var -> Tot exp
let esub_inc_above x y = if y<x then EVar y else EVar (y+1)

val eshift_up_above : nat -> exp -> Tot exp
let eshift_up_above x e = esubst e (esub_inc_above x)

val eshift_up : exp -> Tot exp
let eshift_up = eshift_up_above 0

(* CH: TODO, probably same limitation as above *)
val eshift_up_above_lam: n:nat -> t:typ -> e:exp -> Lemma
  (ensures (eshift_up_above n (ELam t e) = ELam t (eshift_up_above (n + 1) e)))
let eshift_up_above_lam n t e = admit()
(*
  esubst_extensional (esubst_lam (esub_inc_above n)) (esub_inc_above (n+1)) e
*)

(* kinding weakening when a type variable binding is added to env *)
val kinding_weakening_tbnd : #g:env -> #t:typ -> #k:knd ->
      h:(kinding g t k) -> x:var -> k':knd ->
      Tot (kinding (extend_tvar g x k') (tshift_up_above x t) k) (decreases h)
let rec kinding_weakening_tbnd g t k h x k' =
  match h with
    | KiVar a ->
      if a < x then
  	KiVar a
      else
  	KiVar (a + 1)
    | KiLam #g k'' #t1 #k''' h1 ->
      tshift_up_above_lam x k'' t1;
      let h2 = kinding_weakening_tbnd h1 (x + 1) k' in
      KiLam k'' (kinding_extensional h2 (extend_tvar (extend_tvar g x k') 0 k''))
    | KiApp h1 h2 ->
      KiApp (kinding_weakening_tbnd h1 x k') (kinding_weakening_tbnd h2 x k')
    | KiArr h1 h2 ->
      KiArr (kinding_weakening_tbnd h1 x k') (kinding_weakening_tbnd h2 x k')

(* kinding strengthening from TAPL *)
val kinding_strengthening_ebnd : g:env -> x:var -> t_x:typ -> #t:typ -> #k:knd ->
      h:(kinding (extend_evar g x t_x) t k) ->
      Tot (kinding g t k) (decreases h)
let kinding_strengthening_ebnd g x t_x t k h = kinding_extensional h g

(* this folows from functional extensionality *)
val typing_extensional: #g:env -> #e:exp -> #t:typ -> h:(typing g e t) ->
                g':env{FEq (MkEnv.x g) (MkEnv.x g') /\
                       FEq (MkEnv.a g) (MkEnv.a g')} ->
                Tot (typing g' e t) (decreases h)
let rec typing_extensional _ _ _ h g' = h

(* typing weakening when term variable is added to env *)
val typing_weakening_ebnd: #g:env -> x:var -> t_x:typ -> #e:exp -> #t:typ ->
      h:(typing g e t) -> Tot (typing (extend_evar g x t_x)
                                      (eshift_up_above x e) t) (decreases h)
let rec typing_weakening_ebnd g x t_x e t h =
  match h with
    | TyVar y -> if y < x then TyVar y else TyVar (y+1)
    | TyLam #g t_y #e' #t'' kh h21 ->
      eshift_up_above_lam x t_y e';
      let h21 = typing_weakening_ebnd (x+1) t_x h21 in
      TyLam t_y (kinding_extensional kh (extend_evar g x t_x))
                (typing_extensional h21 (extend_evar (extend_evar g x t_x) 0 t_y))
    | TyApp h21 h22 -> TyApp (typing_weakening_ebnd x t_x h21)
                             (typing_weakening_ebnd x t_x h22)
    | TyEqu h1 eq k1 ->
      TyEqu (typing_weakening_ebnd x t_x h1) eq
            (kinding_extensional k1 (extend_evar g x t_x))

val tshift_up_above_e: x:nat -> e:exp -> Tot exp
let rec tshift_up_above_e x e = match e with
  | EVar _ -> e
  | ELam t e1 -> ELam (tshift_up_above x t) (tshift_up_above_e x e1)
  | EApp e1 e2 -> EApp (tshift_up_above_e x e1) (tshift_up_above_e x e2)

val tshift_up_above_tsubst_beta : x:var -> t1:typ -> t2:typ -> Lemma
    (ensures (tshift_up_above x (tsubst_beta t2 t1) =
              tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1)))
    (decreases t1)
let rec tshift_up_above_tsubst_beta x t1 t2 =

  (assert(tshift_up_above x (tsubst_beta t2 t1) =
          tsubst (tsubst_beta t2 t1) (tsub_inc_above x)));
  (assert(tsubst (tsubst_beta t2 t1) (tsub_inc_above x) =

          tsubst (tsubst t1 (tsub_beta_gen 0 t2)) (tsub_inc_above x)));

  (assert(tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1) =
          tsubst (tshift_up_above (x + 1) t1)
                 (tsub_beta_gen 0 (tshift_up_above x t2))));
  (assert(tsubst (tshift_up_above (x + 1) t1)
                 (tsub_beta_gen 0 (tshift_up_above x t2)) =

          tsubst (tsubst t1 (tsub_inc_above (x+1)))
                 (tsub_beta_gen 0 (tsubst t2 (tsub_inc_above x)))));

  match t1 with
  | TVar y -> ()
  | TLam k t ->
     tshift_up_above_lam (x+1) k t;
     tshift_up_above_lam x k (tsubst_beta_gen 1 t2 t); (* this 1 is a bit suspicious *)
     tshift_up_above_tsubst_beta (x+1) t t2;
     admit() (* CH: TODO: crazy without proper reasoning about the hoisting *)
  | TApp t11 t12 -> tshift_up_above_tsubst_beta x t11 t2;
                    tshift_up_above_tsubst_beta x t12 t2
  | TArr t11 t12 -> tshift_up_above_tsubst_beta x t11 t2;
                    tshift_up_above_tsubst_beta x t12 t2

val tequiv_tshift : #t1:typ -> #t2:typ -> h:(tequiv t1 t2) -> x:nat ->
               Tot (tequiv (tshift_up_above x t1) (tshift_up_above x t2))
	       (decreases h)
let rec tequiv_tshift t1 t2 h x =
  match h with
  | EqRefl t -> EqRefl (tshift_up_above x t)
  | EqSymm h1 -> EqSymm (tequiv_tshift h1 x)
  | EqTran h1 h2 -> EqTran (tequiv_tshift h1 x) (tequiv_tshift h2 x)
  | EqLam #t #t' k h1 ->
     tshift_up_above_lam x k t;
     tshift_up_above_lam x k t';
     EqLam k (tequiv_tshift h1 (x+1))
  | EqApp h1 h2 -> EqApp (tequiv_tshift h1 x) (tequiv_tshift h2 x)
  | EqBeta k t1' t2' ->
     tshift_up_above_lam x k t1';
     tshift_up_above_tsubst_beta x t1' t2';
     EqBeta k (tshift_up_above (x+1) t1') (tshift_up_above x t2')
  | EqArr h1 h2 -> EqArr (tequiv_tshift h1 x) (tequiv_tshift h2 x)

(* typing weakening when type variable binding is added to env *)
val typing_weakening_tbnd: #g:env -> x:var -> k_x:knd -> #e:exp -> #t:typ ->
      h:(typing g e t) ->
      Tot (typing (extend_tvar g x k_x) 
                  (tshift_up_above_e x e) (tshift_up_above x t)) (decreases h)
let rec typing_weakening_tbnd g x k_x e t h =
  match h with
    | TyVar y -> TyVar y
    | TyLam #g t' #e1 #t'' kh h1 ->
      TyLam (tshift_up_above x t') (kinding_weakening_tbnd kh x k_x)
            (typing_extensional (typing_weakening_tbnd x k_x h1)
                        (extend_evar (extend_tvar g x k_x) 0
                                     (tshift_up_above x t')))
    | TyApp h1 h2 -> TyApp (typing_weakening_tbnd x k_x h1)
                           (typing_weakening_tbnd x k_x h2)
    | TyEqu h1 eq kh ->
      TyEqu (typing_weakening_tbnd x k_x h1) (tequiv_tshift eq x)
            (kinding_weakening_tbnd kh x k_x)

val esubst_gen_elam : x:var -> v:exp -> t_y:typ -> e':exp -> Lemma
                      (ensures (esubst_beta_gen x v (ELam t_y e') =
                       ELam t_y (esubst_beta_gen (x + 1) (eshift_up v) e')))
let esubst_gen_elam x v t_y e' = admit () (* AR: TODO *)


val typing_substitution: x:nat -> #e:exp -> #v:exp -> #t_x:typ -> #t:typ ->
      #g:env -> h1:(typing g v t_x) -> h2:(typing (extend_evar g x t_x) e t) ->
      Tot (typing g (esubst_beta_gen x v e) t) (decreases %[e;h2])
let rec typing_substitution x e v t_x t g h1 h2 =
  match h2 with
    | TyVar y -> if x = y then h1
      else if y < x then econtext_invariance h2 g
      else TyVar (y - 1)
    | TyLam #g' t_y #e' #t' kh h21 ->
      let h21' = typing_extensional h21 (extend_evar (extend_evar g 0 t_y) (x+1) t_x) in
      let h1' = typing_weakening_ebnd 0 t_y h1 in
      esubst_gen_elam x v t_y e';
      TyLam t_y (kinding_extensional kh g) (typing_substitution (x + 1) h1' h21')
    | TyApp h21 h22 ->
      TyApp (typing_substitution x h1 h21) (typing_substitution x h1 h22)
    | TyEqu h21 eq kh ->
      TyEqu (typing_substitution x h1 h21) eq
        (kinding_strengthening_ebnd g x t_x kh)

val tsubst_gen_tlam : x:var -> t:typ -> k_y:knd -> t':typ -> Lemma
                      (ensures (tsubst_beta_gen x t (TLam k_y t') =
                       TLam k_y (tsubst_beta_gen (x + 1) (tshift_up t) t')))
let tsubst_gen_tlam x t k_y t' = admit () (* AR: TODO *)

(* The (pleasant) surprise here is that (as opposed to TAPS) we didn't
   have to also apply the substitution within the MkEnv.x part of the
   environment. That's because kinding completely ignores that part.
   So we don't even ensure that it's well formed in any way after
   substitution. Unfortunately this joy won't last long. *)
val kinding_substitution: x:nat -> #t1:typ -> #t:typ -> #k_x:knd -> #k1:knd ->
      #g:env -> h1:(kinding g t k_x) ->
      h2:(kinding (extend_tvar g x k_x) t1 k1) ->
      Tot (kinding g (tsubst_beta_gen x t t1) k1) (decreases t1)
let rec kinding_substitution x t1 t k_x k1 g h1 h2 =
  match h2 with
  | KiVar y -> if x=y then h1
               else if y<x then tcontext_invariance h2 g
               else KiVar (y-1)
  | KiLam #g' k_y #t' #k' h21 ->
     (let h21' = kinding_extensional h21 (extend_tvar (extend_tvar g 0 k_y) (x+1) k_x) in
      let h1' = kinding_weakening_tbnd h1 0 k_y in
      let ih = kinding_substitution (x+1) h1' h21' in
      tsubst_gen_tlam x t k_y t';
      KiLam k_y ih)
  | KiApp h21 h22 -> KiApp (kinding_substitution x h1 h21)
                           (kinding_substitution x h1 h22)
  | KiArr h21 h22 ->  KiArr (kinding_substitution x h1 h21)
                            (kinding_substitution x h1 h22)

(* Note: the kind system of LambdaOmega is the same as the type system of STLC.
   So most we should be able to port most things with little changes.
   The main difference is in the way extend works: because types in
   the environment can contain type variables, we need to be a bit
   more careful with shifting indices when adding things. *)

type tred: typ -> typ -> Type =
  | PRefl: t:typ ->
           tred t t

  | PArr:  #t1:typ -> #t2:typ -> #t1':typ -> #t2':typ ->
           tred t1 t1' ->
           tred t2 t2' ->
           tred (TArr t1 t2) (TArr t1' t2')

  | PLam:  #t1:typ -> #t2:typ ->
           k:knd ->
           h:tred t1 t2 ->
           tred (TLam k t1) (TLam k t2)

  | PApp:  #t1:typ -> #t2:typ -> #t1':typ -> #t2':typ ->
           tred t1 t1' ->
           tred t2 t2' ->
           tred (TApp t1 t2) (TApp t1' t2')

  | PBeta: #t1:typ -> #t2:typ -> #t1':typ -> #t2':typ ->
           k:knd ->
           tred t1 t1' ->
           tred t2 t2' ->
           tred (TApp (TLam k t1) t2) (tsubst_beta t2' t1')

(* t => t' implies tshift_up_above x t => tshift_up_above x t' *)
val pred_shiftup_above: #t:typ -> #t':typ -> x:nat -> h:(tred t t') ->
                        Tot (tred (tshift_up_above x t) (tshift_up_above x t'))
		        (decreases h)
let rec pred_shiftup_above t t' x h =
  match h with
    | PRefl t''  -> PRefl (tshift_up_above x t'')
    | PArr h1 h2 -> PArr (pred_shiftup_above x h1) (pred_shiftup_above x h2)
    | PLam #t1 #t2 k h1  ->
      tshift_up_above_lam x k t1;
      tshift_up_above_lam x k t2;
      PLam k (pred_shiftup_above (x + 1) h1)
    | PApp h1 h2 -> PApp (pred_shiftup_above x h1) (pred_shiftup_above x h2)
    | PBeta #t1 #t2 #t1' #t2' k h1 h2 ->
      tshift_up_above_lam x k t1;
      tshift_up_above_tsubst_beta x t1' t2';
      PBeta k (pred_shiftup_above (x + 1) h1) (pred_shiftup_above x h2)

(* s => s' implies t[y |-> s] => t[y |-> s'] *)
val subst_of_pred: #s:typ -> #s':typ -> x:nat -> t:typ ->
                   h:(tred s s') ->
                   Tot (tred (tsubst_beta_gen x s t) (tsubst_beta_gen x s' t))
		   (decreases t)
let rec subst_of_pred s s' x t h =
  match t with
    | TVar y ->
      if y < x then
  	PRefl t
      else if y = x then
  	h
      else
  	PRefl (TVar (y - 1))
    | TLam k t1 ->
      tsubst_gen_tlam x s k t1;
      tsubst_gen_tlam x s' k t1;
      PLam k (subst_of_pred (x + 1) t1 (pred_shiftup_above 0 h))
    | TApp t1 t2 ->
      PApp (subst_of_pred x t1 h) (subst_of_pred x t2 h)
    | TArr t1 t2 ->
      PArr (subst_of_pred x t1 h) (subst_of_pred x t2 h)


val commute_tsubst: t1:typ -> y:nat -> t2:typ -> x:nat -> s:typ -> Lemma
                    (ensures (tsubst_beta_gen x s (tsubst_beta_gen y t2 t1) =
                              tsubst_beta_gen y (tsubst_beta_gen x s t2)
                                (tsubst_beta_gen (x + 1) (tshift_up_above y s) t1)))
let commute_tsubst t1 y t2 x s = admit () (* AR: TODO *)


(* t => t' and s => s' implies t[x |-> s] => t'[x |-> s'] *)
val subst_of_pred_pred: #s:typ -> #s':typ -> #t:typ -> #t':typ -> x:nat ->
                       hs:(tred s s') -> ht:(tred t t') ->
                       Tot (tred (tsubst_beta_gen x s t) (tsubst_beta_gen x s' t'))
                       (decreases ht)
let rec subst_of_pred_pred s s' t t' x hs ht =
  match ht with
    | PRefl t1 -> subst_of_pred x t1 hs
    | PArr ht1 ht2 ->
      PArr (subst_of_pred_pred x hs ht1) (subst_of_pred_pred x hs ht2)
    | PLam #t1 #t2 k ht1 ->
      tsubst_gen_tlam x s k t1;
      tsubst_gen_tlam x s' k t2;
      PLam k (subst_of_pred_pred (x + 1) (pred_shiftup_above 0 hs) ht1)
    | PApp h1 h2 ->
      PApp (subst_of_pred_pred x hs h1) (subst_of_pred_pred x hs h2)
    | PBeta #t1 #t2 #t1' #t2' k ht1 ht2 ->
      tsubst_gen_tlam x s k t1;
      let ht1' = subst_of_pred_pred (x + 1) (pred_shiftup_above 0 hs) ht1 in
      let ht2' = subst_of_pred_pred x hs ht2 in
      commute_tsubst t1' 0 t2' x s';
      PBeta k ht1' ht2'

type ltup =
  | MkLTup: #s:typ -> #t:typ -> #u:typ -> (tred s t) -> (tred s u) -> ltup

(* single step diamond property of parallel reduction *)
val pred_diamond: #s:typ -> #t:typ -> #u:typ ->
                  h1:(tred s t) -> h2:(tred s u) ->
                  Tot (ex (fun v -> cand (tred t v) (tred u v)))
                  (decreases %[h1;h2])
let rec pred_diamond s t u h1 h2 =
  match (MkLTup h1 h2) with
    | MkLTup (PRefl t1) _ -> ExIntro u (Conj h2 (PRefl u))
    | MkLTup _ (PRefl t1) -> ExIntro t (Conj (PRefl t) h1)
  (* if one is PLam, the other has to be PLam *)
    | MkLTup (PLam k h11) (PLam _ h12) ->
    (* AR: p only has one constructor Conj,
           but direct pattern matching doesn't work *)
      let ExIntro t' p = pred_diamond h11 h12 in
      (match p with
  	| Conj pa pb -> ExIntro (TLam k t') (Conj (PLam k pa) (PLam k pb)))
  (* if one is PArr, the other has to be PArr *)
    | MkLTup (PArr h11 h12) (PArr h21 h22) ->
      let ExIntro v1 p1 = pred_diamond h11 h21 in
      let ExIntro v2 p2 = pred_diamond h12 h22 in
      
      (match p1 with
  	| Conj p1a p1b ->
  	  (match p2 with
  	    | Conj p2a p2b ->
  	      ExIntro (TArr v1 v2) (Conj (PArr p1a p2a) (PArr p1b p2b))))
  (* both PApp *)
    | MkLTup (PApp h11 h12) (PApp h21 h22) ->
      let ExIntro v1 p1 = pred_diamond h11 h21 in
      let ExIntro v2 p2 = pred_diamond h12 h22 in
      
      (match p1 with
  	| Conj p1a p1b ->
  	  (match p2 with
  	    | Conj p2a p2b ->
  	      ExIntro (TApp v1 v2) (Conj (PApp p1a p2a) (PApp p1b p2b))))
  (* both PBeta *)
    | MkLTup (PBeta #s1 #s2 #t1' #t2' k h11 h12)
             (PBeta #s11 #s21 #u1' #u2' k' h21 h22) ->
      let ExIntro v1 p1 = pred_diamond h11 h21 in
      let ExIntro v2 p2 = pred_diamond h12 h22 in

      (match p1 with
  	| Conj p1a p1b ->
  	  (match p2 with
  	    | Conj p2a p2b ->
  	      ExIntro (tsubst_beta_gen 0 v2 v1)
                      (Conj (subst_of_pred_pred 0 p2a p1a)
                            (subst_of_pred_pred 0 p2b p1b))))
  (* one PBeta and other PApp *)
    | MkLTup (PBeta #s1 #s2 #t1' #t2' k h11 h12)
             (PApp #s1' #s2' #lu1' #u2' h21 h22) ->
    (* AR: does not work without this type annotation *)
      let h21:(tred (TLam.t s1') (TLam.t lu1')) = match h21 with
  	| PLam _ h' -> h'
  	| PRefl _ -> PRefl (TLam.t s1')
      in
      
      let ExIntro v1 p1 = pred_diamond h11 h21 in
      let ExIntro v2 p2 = pred_diamond h12 h22 in

      (match p1 with
  	| Conj p1a p1b ->
  	  (match p2 with
  	    | Conj p2a p2b ->
  	      let v = tsubst_beta_gen 0 v2 v1 in
  	      ExIntro v (Conj (subst_of_pred_pred 0 p2a p1a) (PBeta k p1b p2b))))
    | MkLTup (PApp #s1' #s2' #lu1' #u2' h21 h22)
             (PBeta #s1 #s2 #t1' #t2' k h11 h12) ->
    (* similar to above case *)
      admit ()

type tred_star: typ -> typ -> Type =
  | PcBase:  t:typ ->
             tred_star t t

  | PcTrans: #t1:typ -> #t2:typ -> #t3:typ ->
             tred         t1 t2 ->
             tred_star t2 t3 ->
             tred_star t1 t3

val tred_star_one_loop: #s:typ -> #t:typ -> #u:typ ->
      h:(tred s t) -> hs:(tred_star s u) ->
      Tot (ex (fun v -> cand (tred_star t v) (tred u v))) (decreases hs)
let rec tred_star_one_loop s t u h hs = match hs with
  | PcBase _ ->
    ExIntro t (Conj (PcBase t) h)
  | PcTrans #s #u1 #u h1 hs' ->
    let ExIntro v1 p1 = pred_diamond h h1 in
    let Conj p1a p1b = p1 in
    let ExIntro v p2 = tred_star_one_loop p1b hs' in
    let Conj p2a p2b = p2 in
    ExIntro v (Conj (PcTrans p1a p2a) (p2b))

(* aka Church-Rosser *)
val confluence : #s:typ -> #t:typ -> #u:typ ->
      h1:(tred_star s t) -> h2:(tred_star s u) ->
      Tot (ex (fun v -> cand (tred_star t v) (tred_star u v)))
      (decreases h1)
let rec confluence s t u h1 h2 =
  match h1 with
  | PcBase _ ->
    ExIntro u (Conj h2 (PcBase u))
  | PcTrans #s #t1 #t h1' hs1 ->
     let ExIntro v1 p = tred_star_one_loop h1' h2 in
     let Conj p1 p2 = p in
     let ExIntro v p' = confluence hs1 p1 in
     let Conj p1' p2' = p' in
     ExIntro v (Conj p1' (PcTrans p2 p2'))

assume val proposition_30_3_10 : #t:typ -> #s:typ ->
      tred_star s t ->
      tred_star t s ->
      Tot (ex (fun u -> cand (tred_star s u) (tred_star t u)))

(* the TAPL proof for this is rather informal *)
val lemma_30_3_5_ltr : #s:typ -> #t:typ -> tequiv s t ->
      Tot (cand (tred_star s t) (tred_star t s))
let lemma_30_3_5_ltr s t = admit()

(* TAPL calls this direction obvious, it's also apparently not used below? *)
val lemma_30_3_5_rtl : #s:typ -> #t:typ ->
      tred_star s t -> tred_star t s -> Tot (tequiv s t)
let lemma_30_3_5_rtl s t = admit()

val corrolary_30_3_11 : #s:typ -> #t:typ ->
      tequiv s t ->
      Tot (ex (fun u -> cand (tred_star s u) (tred_star t u)))
let corrolary_30_3_11 s t h =
  let Conj h1 h2 = lemma_30_3_4_ltr h in
  proposition_30_3_10 h1 h2

assume val tred_tarr_preserved : #s1:typ -> #s2:typ -> #t:typ ->
      tred_star (TArr s1 s2) t ->
      Tot (ex (fun t1 -> ex (fun t2 -> cand (t = TArr t1 t2)
                        (cand (tred_star s1 t1) (tred_star s2 t2)))))

assume val inversion_elam : #g:env -> s1:typ -> e:exp ->
      #s:typ -> t1:typ -> t2:typ -> typing g (ELam s1 e) s ->
      tequiv s (TArr t1 t2) ->
      Tot (cand (tequiv t1 s1) (typing (extend_evar g 0 t1) e t2))

(* corollary of inversion_elam *)
val inversion_elam_typing : #g:env -> s1:typ -> e:exp ->
      t1:typ -> t2:typ -> typing g (ELam s1 e) (TArr t1 t2) ->
      Tot (typing (extend_evar g 0 t1) e t2)
let inversion_elam_typing _ s1 e t1 t2 h =
  let Conj _ hr = inversion_elam s1 e t1 t2 h (EqRefl (TArr t1 t2)) in hr

(* Type preservation *)

val preservation : #e:exp -> #e':exp -> hs:step e e' ->
                   #g:env -> #t:typ -> ht:(typing g e t) ->
                   Tot (typing g e' t) (decreases ht)
let rec preservation _ _ hs _ _ ht =
  match ht with
  | TyApp #g #e1 #e2 #t1 #t2 h1 h2 ->
    (match hs with
     | SBeta s1 e11 e12 ->
        typing_substitution 0 h2 (inversion_elam_typing s1 e11 t1 t2 h1)
     | SApp1 e2' hs1   -> TyApp (preservation hs1 h1) h2
     | SApp2 e1' hs2   -> TyApp h1 (preservation hs2 h2))
  | TyEqu ht1 he hk -> TyEqu (preservation hs ht1) he hk
