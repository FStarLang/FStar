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
       if y=0 
       then EVar y 
       else (esubst (s (y - 1)) esub_inc) in
     ELam t (esubst e1 subst_elam)
     
  | EApp e1 e2 -> EApp (esubst e1 s) (esubst e2 s)

val esubst_lam: s:esub -> Tot esub
let esubst_lam s y =
  if y = 0 then EVar y
  else esubst (s (y-1)) esub_inc

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
            #t1:typ ->
            #k':knd ->
            kinding (extend_tvar g 0 k) t1 k' ->
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

(* Substitution extensional; trivial with the extensionality axiom *)

val subst_extensional: s1:esub -> s2:esub{FEq s1 s2} -> e:exp ->
                       Lemma (esubst e s1 = esubst e s2)
let subst_extensional s1 s2 e = ()

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
type xand : Type -> Type -> Type =
  | Conj : #a:Type -> #b:Type -> pa:a -> pb:b -> xand a b
type xiff (a : Type) (b : Type) = xand (a -> Tot b) (b -> Tot a)

val id : 'a -> Tot 'a
let id x = x

val fcomp : ('a -> Tot 'b) -> ('b -> Tot 'c) -> 'a -> Tot 'c
let fcomp f1 f2 a = f2 (f1 a)

val kinding_tequiv : #g:env -> #t1:typ -> #t2:typ -> #k:knd -> h:(tequiv t1 t2) ->
      Tot (xiff (kinding g t1 k) (kinding g t2 k)) (decreases h)
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


val esub_inc_above : nat -> var -> Tot exp
let esub_inc_above x y = if y<x then EVar y else EVar (y+1)

val eshift_up_above : nat -> exp -> Tot exp
let eshift_up_above x e = esubst e (esub_inc_above x)

val eshift_up : exp -> Tot exp
let eshift_up = eshift_up_above 0

val eshift_up_above_lam: n:nat -> t:typ -> e:exp -> Lemma
  (ensures (eshift_up_above n (ELam t e) = ELam t (eshift_up_above (n + 1) e)))
let eshift_up_above_lam n t e = admit () (* AR: TODO *)

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

val tshift_eq: #s:typ -> #t:typ -> h:(tequiv s t) -> x:nat ->
               Tot (tequiv (tshift_up_above x s) (tshift_up_above x t))
	       (decreases h)
let tshift_eq s t h = admit () (* AR: TODO *)

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
      TyEqu (typing_weakening_tbnd x k_x h1) (tshift_eq eq x)
            (kinding_weakening_tbnd kh x k_x)

val esubst_gen_elam : x:var -> v:exp -> t_y:typ -> e':exp -> Lemma
                      (ensures (esubst_beta_gen x v (ELam t_y e') =
                       ELam t_y (esubst_beta_gen (x + 1) (eshift_up v) e')))
let esubst_gen_elam x v t_y e' = admit () (* AR: TODO *)


val substitution_lemma_e: x:nat -> #e:exp -> #v:exp -> #t_x:typ -> #t:typ ->
      #g:env -> h1:(typing g v t_x) -> h2:(typing (extend_evar g x t_x) e t) ->
      Tot (typing g (esubst_beta_gen x v e) t) (decreases %[e;h2])
let rec substitution_lemma_e x e v t_x t g h1 h2 = match h2 with
  | TyVar y -> if x = y then h1
               else if y < x then econtext_invariance h2 g
               else TyVar (y - 1)
  | TyLam #g' t_y #e' #t' kh h21 ->
    let h21' = typing_extensional h21 (extend_evar (extend_evar g 0 t_y) (x + 1) t_x) in
    let h1' = typing_weakening_ebnd 0 t_y h1 in
    esubst_gen_elam x v t_y e';
    TyLam t_y (kinding_extensional kh g) (substitution_lemma_e (x + 1) h1' h21')
  | TyApp h21 h22 ->
    TyApp (substitution_lemma_e x h1 h21) (substitution_lemma_e x h1 h22)
  | TyEqu h21 eq kh ->
    TyEqu (substitution_lemma_e x h1 h21) eq
          (kinding_strengthening_ebnd g x t_x kh)

val substitution_lemma_t: x:nat -> #t1:typ -> #t:typ -> #k_x:knd -> #k1:knd ->
      #g:env -> h1:(kinding g t k_x) ->
      h2:(kinding (extend_tvar g x k_x) t1 k1) ->
      Tot (kinding g (tsubst_beta_gen x t t1) k1) (decreases t1)
let rec substitution_lemma_t x t1 t k_x k1 g h1 h2 = match h2 with
  | _ -> admit ()

(* Note: the kind system of LambdaOmega is the same as the type system of STLC.
   So most we should be able to port most things with little changes.
   The main difference is in the way extend works: because types in
   the environment can contain type variables, we need to be a bit
   more careful with shifting indices when adding things. *)
