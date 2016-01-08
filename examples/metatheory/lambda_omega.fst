(*--build-config
    options: --admit_fsi FStar.Set --max_fuel 1 --max_ifuel 1 --initial_fuel 1;
    other-files: FStar.Constructive.fst FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
  --*)
(*
   Copyright 2015
     Simon Forest - Inria and ENS Paris
     Catalin Hritcu - Inria
     Aseem Rastogi - UMD
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

module LambdaOmega

open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality

(* Chapter 29 of TAPL: "Type Operators and Kinding",
   proof follows Chapter 30, but we don't consider polymorphism
   (for extension to System F-omega see f-omega.fst) *)

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

(* Substitution on expressions
   (in this calculus doesn't interact with type substitution below) *)

type esub = var -> Tot exp
type erenaming (s:esub) = (forall (x:var). is_EVar (s x))

val is_erenaming : s:esub -> GTot (n:int{(  erenaming s  ==> n=0) /\
                                         (~(erenaming s) ==> n=1)})
let is_erenaming s = (if excluded_middle (erenaming s) then 0 else 1)

val esub_inc : var -> Tot exp
let esub_inc y = EVar (y+1)

let is_evar (e:exp) : int = if is_EVar e then 0 else 1

val esubst : s:esub -> e:exp -> Pure exp (requires True)
      (ensures (fun e' -> erenaming s /\ is_EVar e ==> is_EVar e'))
      (decreases %[is_evar e; is_erenaming s; 1; e])

val esub_lam: s:esub -> x:var -> Tot (e:exp{ erenaming s ==> is_EVar e})
      (decreases %[1;is_erenaming s; 0; EVar 0])

let rec esubst s e =
  match e with
  | EVar x -> s x
  | ELam t e -> ELam t (esubst (esub_lam s) e)
  | EApp e1 e2 -> EApp (esubst s e1) (esubst s e2)
and esub_lam s = fun y ->
  if y = 0 then EVar y
           else esubst esub_inc (s (y-1))

val esub_lam_renaming: s:esub -> Lemma
  (ensures (forall (x:var). erenaming s ==> is_EVar (esub_lam s x)))
let esub_lam_renaming s = ()

(* Substitution extensional; trivial with the extensionality axiom *)
val esubst_extensional: s1:esub -> s2:esub{FEq s1 s2} -> e:exp ->
                        Lemma (requires True) (ensures (esubst s1 e = esubst s2 e))
                       (*[SMTPat (esubst s1 e);  SMTPat (esubst s2 e)]*)
let esubst_extensional s1 s2 e = ()

(* This only works automatically with the patterns in subst_extensional above;
   it would be a lot cooler if this worked without, since that increases checking time.
   Even worse, there is no way to prove this without the SMTPat (e.g. manually),
   or to use the SMTPat only locally, in this definition (`using` needed). *)
val esub_lam_hoist : t:typ -> e:exp -> s:esub -> Lemma (requires True)
      (ensures (esubst s (ELam t e) = ELam t (esubst (esub_lam s) e)))
      (* [SMTPat (esubst (ELam t e) s)]
      (\* -- this increases running time by 10 secs and adds variability *\) *)
let esub_lam_hoist t e s = admit()
  // using esubst_extensional
  //   (fun s1 s2 e -> [SMTPat (esubst s1 e);  SMTPat (esubst s2 e)])

val esub_beta : exp -> Tot esub
let esub_beta e = fun y -> if y = 0 then e
                           else (EVar (y-1))

val esubst_beta : exp -> exp -> Tot exp
let esubst_beta e = esubst (esub_beta e)

(* Substitution on types is kind of analogous *)
(* CH: Now this is more complex: tsub_inc_above, tsubst_beta_gen are
   still there unfortunately, although they were simplified away for
   expressions. This seems to be more an artifact of the TAPL proof
   (via confluence); so we can still hope we can do better for TinyF*.*)

type tsub = var -> Tot typ
type trenaming (s:tsub) = (forall (x:var). is_TVar (s x))

val is_trenaming : s:tsub -> GTot (n:int{(  trenaming s  ==> n=0) /\
                                         (~(trenaming s) ==> n=1)})
let is_trenaming s = (if excluded_middle (trenaming s) then 0 else 1)

val tsub_inc_above : nat -> var -> Tot typ
let tsub_inc_above x y = if y<x then TVar y else TVar (y+1)

val tsub_inc : var -> Tot typ
let tsub_inc = tsub_inc_above 0

val trenaming_sub_inc : unit -> Lemma (trenaming (tsub_inc))
let trenaming_sub_inc _ = ()

let is_tvar (t:typ) : int = if is_TVar t then 0 else 1

val tsubst : s:tsub -> t:typ -> Pure typ (requires True)
      (ensures (fun t' -> trenaming s /\ is_TVar t ==> is_TVar t'))
      (decreases %[is_tvar t; is_trenaming s; t])
let rec tsubst s t =
  match t with
  | TVar x -> s x

  | TLam k t1 ->
     let tsub_lam : y:var -> Tot (t:typ{trenaming s ==> is_TVar t}) =
       fun y -> if y=0 then TVar y
                       else (tsubst tsub_inc (s (y-1))) in
     TLam k (tsubst tsub_lam t1)

  | TArr t1 t2 -> TArr (tsubst s t1) (tsubst s t2)
  | TApp t1 t2 -> TApp (tsubst s t1) (tsubst s t2)

val tsub_lam: s:tsub -> Tot tsub
let tsub_lam s y =
  if y = 0 then TVar y
           else tsubst tsub_inc (s (y-1))

(* Type substitution extensional; trivial with the extensionality axiom *)
val tsubst_extensional: s1:tsub -> s2:tsub{FEq s1 s2} -> t:typ ->
                        Lemma (requires True) (ensures (tsubst s1 t = tsubst s2 t))
(*                       [SMTPat (tsubst t s1);  SMTPat (tsubst t s2)]*)
let tsubst_extensional s1 s2 t = ()

(* Same silly situation as for esub_lam_hoist *)
val tsub_lam_hoist : k:knd -> t:typ -> s:tsub -> Lemma
      (ensures (tsubst s (TLam k t) = TLam k (tsubst (tsub_lam s) t)))
let tsub_lam_hoist k t s = admit()

(* Type substitution composition *)
(* CH: again, we managed to get rid of this for expressions only
       (it was never used anyway) *)

val tsub_comp : s1:tsub -> s2:tsub -> Tot tsub
let tsub_comp s1 s2 x = tsubst s1 (s2 x)

val tsub_comp_inc : s:tsub -> x:var ->
      Lemma (tsub_comp tsub_inc s x = tsub_comp (tsub_lam s) tsub_inc x)
let tsub_comp_inc s x = ()

val tsub_lam_renaming: s:tsub -> Lemma
  (ensures (forall (x:var). trenaming s ==> is_TVar (tsub_lam s x)))
let tsub_lam_renaming s = ()

val tsubst_comp : s1:tsub -> s2:tsub -> t:typ -> Lemma
      (tsubst s1 (tsubst s2 t) = tsubst (tsub_comp s1 s2) t)
      (decreases %[is_tvar t;
                   is_trenaming s1;
                   is_trenaming s2;
                   t])
let rec tsubst_comp s1 s2 t =
  match t with
  | TVar z -> ()
  | TApp t1 t2 -> tsubst_comp s1 s2 t1; tsubst_comp s1 s2 t2
  | TLam k tbody ->
      let tsub_lam_comp : x:var ->
            Lemma(tsub_lam (tsub_comp s1 s2) x =
                            tsub_comp (tsub_lam s1) (tsub_lam s2) x) =
        fun x -> match x with
        | 0 -> ()
        | _ -> begin
          let ih1 = trenaming_sub_inc ();
                    tsubst_comp tsub_inc s1 (s2 (x-1)) in
          let ext = forall_intro (tsub_comp_inc s1);
                    tsubst_extensional (tsub_comp tsub_inc s1)
                                       (tsub_comp (tsub_lam s1) tsub_inc)
                                       (s2 (x-1)) in
          let ih2 = tsub_lam_renaming s1;
                    trenaming_sub_inc ();
                    tsubst_comp (tsub_lam s1) tsub_inc (s2 (x-1))
          in ()
        end
      in
      let hoist1 = tsub_lam_hoist k tbody s2 in
      let hoist2 = tsub_lam_hoist k (tsubst (tsub_lam s2) tbody) s1 in
    let h1 =
      tsub_lam_renaming s1;
      tsub_lam_renaming s2;
      tsubst_comp (tsub_lam s1) (tsub_lam s2) tbody in

    let h2 =
      forall_intro tsub_lam_comp;
      cut (FEq (tsub_comp (tsub_lam s1) (tsub_lam s2))
             (tsub_lam (tsub_comp s1 s2))) in

    let ext = tsubst_extensional
      (tsub_comp (tsub_lam s1) (tsub_lam s2))
      (tsub_lam (tsub_comp s1 s2))
      tbody in

    tsub_lam_hoist k tbody (tsub_comp s1 s2)

  | TArr t1 t2 -> tsubst_comp s1 s2 t1; tsubst_comp s1 s2 t2

val tsub_lam_comp : s1:tsub -> s2:tsub -> x:var -> Lemma
      (tsub_lam (tsub_comp s1 s2) x = tsub_comp (tsub_lam s1) (tsub_lam s2) x)
(* CH: TODO: Quite a bit of duplication here, mutual recursion would
       have been better than nested one. Can we do that? *)
let tsub_lam_comp s1 s2 x =
        match x with
        | 0 -> ()
        | _ -> begin
          let ih1 = trenaming_sub_inc ();
                    tsubst_comp tsub_inc s1 (s2 (x-1)) in
          let ext = forall_intro (tsub_comp_inc s1);
                    tsubst_extensional (tsub_comp tsub_inc s1)
                                       (tsub_comp (tsub_lam s1) tsub_inc)
                                       (s2 (x-1)) in
          let ih2 = tsub_lam_renaming s1;
                    trenaming_sub_inc ();
                    tsubst_comp (tsub_lam s1) tsub_inc (s2 (x-1))
          in ()
        end

(* Identity substitution *)

val tsub_id : tsub
let tsub_id x = TVar x

val tsubst_id : t:typ -> Lemma (tsubst tsub_id t = t)
let rec tsubst_id t =
  match t with
  | TVar z -> ()
  | TLam k t1 ->
     tsub_lam_hoist k t1 tsub_id;
     tsubst_extensional tsub_id (tsub_lam tsub_id) t1;
     tsubst_id t1
  | TArr t1 t2
  | TApp t1 t2 -> tsubst_id t1; tsubst_id t2

(* Beta *)

val tsub_beta_gen : var -> typ -> Tot tsub
let tsub_beta_gen x t = fun y -> if y < x then (TVar y)
                                 else if y = x then t
                                 else (TVar (y-1))

val tsubst_beta_gen : var -> typ -> typ -> Tot typ
let tsubst_beta_gen x t' t = tsubst (tsub_beta_gen x t') t

let tsubst_beta t' t = tsubst_beta_gen 0 t' t

(* Shifting *)

val tshift_up_above : nat -> typ -> Tot typ
let tshift_up_above x = tsubst (tsub_inc_above x)

val tshift_up : typ -> Tot typ
let tshift_up = tshift_up_above 0

(* Step relation -- going for strong reduction, just because we can *)

type step : exp -> exp -> Type =
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp ->
            step (EApp (ELam t e1) e2) (esubst_beta e2 e1)
  | SApp1 : #e1:exp ->
             e2:exp ->
            #e1':exp ->
            =hst:(step e1 e1') ->
             step (EApp e1 e2) (EApp e1' e2)
  | SApp2 :  e1:exp ->
            #e2:exp ->
            #e2':exp ->
            =hst:(step e2 e2') ->
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
            =hk:kinding (extend_tvar g 0 k) t k' ->
                kinding g (TLam k t) (KArr k k')
  | KiApp : #g:env ->
            #t1:typ ->
            #t2:typ ->
            #k11:knd ->
            #k12:knd ->
            =hk1:kinding g t1 (KArr k11 k12) ->
            =hk2:kinding g t2 k11 ->
                 kinding g (TApp t1 t2) k12
  | KiArr : #g:env ->
            #t1:typ ->
            #t2:typ ->
            =hk1:kinding g t1 KTyp ->
            =hk2:kinding g t2 KTyp ->
                 kinding g (TArr t1 t2) KTyp

type tequiv : typ -> typ -> Type =
  | EqRefl : t:typ ->
             tequiv t t
  | EqSymm : #t1:typ ->
             #t2:typ ->
             =he:tequiv t1 t2 ->
             tequiv t2 t1
  | EqTran : #t1:typ ->
             #t2:typ ->
             #t3:typ ->
             =he12:tequiv t1 t2 ->
             =he23:tequiv t2 t3 ->
                   tequiv t1 t3
  | EqLam : #t :typ ->
            #t':typ ->
             k :knd ->
            =he:tequiv t t' ->
                tequiv (TLam k t) (TLam k t')
  | EqApp : #t1 :typ ->
            #t1':typ ->
            #t2 :typ ->
            #t2':typ ->
            =he1:tequiv t1 t1' ->
            =he2:tequiv t2 t2' ->
                 tequiv (TApp t1 t2) (TApp t1' t2')
  | EqBeta :k:knd ->
            t1:typ ->
            t2:typ ->
            tequiv (TApp (TLam k t1) t2) (tsubst_beta t2 t1)
  | EqArr : #t1 :typ ->
            #t1':typ ->
            #t2 :typ ->
            #t2':typ ->
            =he1:tequiv t1 t1' ->
            =he2:tequiv t2 t2' ->
                 tequiv (TArr t1 t2) (TArr t1' t2')

type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
             x:var{is_Some (lookup_evar g x)} ->
            =hk:kinding g (Some.v (lookup_evar g x)) KTyp ->
                typing g (EVar x) (Some.v (lookup_evar g x))
  | TyLam : #g:env ->
             t:typ ->
            #e1:exp ->
            #t':typ ->
            =hk:kinding g t KTyp ->
            =ht:typing (extend_evar g 0 t) e1 t' ->
                typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t1:typ ->
            #t2:typ ->
            =ht1:typing g e1 (TArr t1 t2) ->
            =ht2:typing g e2 t1 ->
                 typing g (EApp e1 e2) t2
  | TyEqu : #g:env ->
            #e:exp ->
            #t1:typ ->
            #t2:typ ->
            =ht:typing g e t1 ->
            =he:tequiv t1 t2 ->
            =hk:kinding g t2 KTyp ->
                typing g e t2

(* Progress proof *)

val is_value : exp -> Tot bool
let is_value = is_ELam

opaque val progress : #e:exp -> #t:typ -> h:typing empty e t ->
               Pure (cexists (fun e' -> step e e'))
                    (requires (not (is_value e)))
                    (ensures (fun _ -> True)) (decreases h)
let rec progress _ _ h =
  match h with
    | TyApp #g #e1 #e2 #t11 #t12 h1 h2 ->
      (match e1 with
       | ELam t e1' -> ExIntro (esubst_beta e2 e1') (SBeta t e1' e2)
       | _ -> (match progress h1 with
                | ExIntro e1' h1' -> ExIntro (EApp e1' e2) (SApp1 e2 h1')))
    | TyEqu h1 _ _ -> progress h1

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

opaque val tcontext_invariance : #t:typ -> #g:env -> #k:knd ->
                          h:(kinding g t k) -> g':env{EnvEqualT t g g'} ->
                          Tot (kinding g' t k) (decreases h)
let rec tcontext_invariance _ _ _ h g' =
  match h with
  | KiVar a -> KiVar a
  | KiLam k1 h1 -> KiLam k1 (tcontext_invariance h1 (extend_tvar g' 0 k1))
  | KiApp h1 h2 -> KiApp (tcontext_invariance h1 g') (tcontext_invariance h2 g')
  | KiArr h1 h2 -> KiArr (tcontext_invariance h1 g') (tcontext_invariance h2 g')
(* CH: this doesn't directly follow from functional extensionality,
       because (MkEnv.x g) and (MkEnv.x g') are completely unrelated;
       this is just because we pass this useless argument to kinding. *)
opaque val kinding_extensional: #g:env -> #t:typ -> #k:knd -> h:(kinding g t k) ->
                g':env{FEq (MkEnv.a g) (MkEnv.a g')} ->
                Tot (kinding g' t k) (decreases h)
let rec kinding_extensional _ _ _ h g' =
  match h with
    | KiVar a -> KiVar a
    | KiLam k1 h1 -> KiLam k1 (kinding_extensional h1 (extend_tvar g' 0 k1))
    | KiApp h1 h2 -> KiApp (kinding_extensional h1 g') (kinding_extensional h2 g')
    | KiArr h1 h2 -> KiArr (kinding_extensional h1 g') (kinding_extensional h2 g')

(* kinding weakening when a term variable binding is added to env *)
opaque val kinding_weakening_ebnd : #g:env -> #t:typ -> #k:knd ->
      h:(kinding g t k) -> x:var -> t':typ ->
      Tot (kinding (extend_evar g x t') t k)
let kinding_weakening_ebnd g t k h x t' =
  kinding_extensional h (extend_evar g x t')

val tshift_up_above_lam: n:nat -> k:knd -> t:typ -> Lemma
  (ensures (tshift_up_above n (TLam k t) = TLam k (tshift_up_above (n + 1) t)))
let tshift_up_above_lam n k t =
  assert(tshift_up_above n (TLam k t) = tsubst (tsub_inc_above n) (TLam k t));
  tsub_lam_hoist k t (tsub_inc_above n);
  assert(tshift_up_above n (TLam k t) =
         TLam k (tsubst (tsub_lam (tsub_inc_above n)) t));
  tsubst_extensional (tsub_lam (tsub_inc_above n)) (tsub_inc_above (n+1)) t

(* kinding weakening when a type variable binding is added to env *)
opaque val kinding_weakening_tbnd : #g:env -> #t:typ -> #k:knd ->
      h:(kinding g t k) -> x:var -> k':knd ->
      Tot (kinding (extend_tvar g x k') (tshift_up_above x t) k) (decreases h)
let rec kinding_weakening_tbnd g t k h x k' =
  match h with
    | KiVar a -> if a < x then KiVar a
                          else KiVar (a + 1)
    | KiLam #g k'' #t1 #k''' h1 ->
      tshift_up_above_lam x k'' t1;
      let h2 = kinding_weakening_tbnd h1 (x + 1) k' in
      KiLam k'' (kinding_extensional h2 (extend_tvar (extend_tvar g x k') 0 k''))
    | KiApp h1 h2 ->
      KiApp (kinding_weakening_tbnd h1 x k') (kinding_weakening_tbnd h2 x k')
    | KiArr h1 h2 ->
      KiArr (kinding_weakening_tbnd h1 x k') (kinding_weakening_tbnd h2 x k')

(* kinding strengthening from TAPL (Lemma 30.3.1),
   just an instance of kinding_extensional; used often *)
opaque val kinding_strengthening_ebnd :
      g:env -> x:var -> t_x:typ -> #t:typ -> #k:knd ->
      h:(kinding (extend_evar g x t_x) t k) ->
      Tot (kinding g t k) (decreases h)
let kinding_strengthening_ebnd g x t_x t k h = kinding_extensional h g

opaque val kinding_inversion_arrow: #g:env -> #t1:typ -> #t2:typ ->
                             h:(kinding g (TArr t1 t2) KTyp) ->
                             Tot (cand (kinding g t1 KTyp) (kinding g t2 KTyp))
let rec kinding_inversion_arrow g t1 t2 h = match h with
  | KiArr h1 h2 -> Conj h1 h2

opaque val typing_to_kinding : #g:env -> #e:exp -> #t:typ ->
                                    h:(typing g e t) ->
                                    Tot (kinding g t KTyp) (decreases h)
let rec typing_to_kinding g e t h = match h with
  | TyVar x h -> h
  | TyLam t' hk h1 -> KiArr hk (kinding_strengthening_ebnd g 0 t'
                                  (typing_to_kinding h1))
  | TyApp #g #e1 #e2 #t1 #t2 h1 h2 ->
    Conj.h2 (kinding_inversion_arrow #g #t1 #t2 (typing_to_kinding h1))
  | TyEqu h1 eq hk -> hk

(* this folows from functional extensionality *)
val tshift_up_above_tsubst_beta_aux : x:var -> t2:typ -> y:var ->
      Lemma (tsub_comp (tsub_inc_above x) (tsub_beta_gen 0 t2) y =
             tsub_comp (tsub_beta_gen 0 (tsubst (tsub_inc_above x) t2))
                       (tsub_inc_above (x+1)) y)
let tshift_up_above_tsubst_beta_aux x t2 y = ()

val tshift_up_above_tsubst_beta : x:var -> t1:typ -> t2:typ -> Lemma
    (ensures (tshift_up_above x (tsubst_beta t2 t1) =
              tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1)))
    (decreases t1)
let rec tshift_up_above_tsubst_beta x t1 t2 =

  assert(tshift_up_above x (tsubst_beta t2 t1) =
         tsubst (tsub_inc_above x) (tsubst_beta t2 t1));
  assert(tshift_up_above x (tsubst_beta t2 t1) =
         tsubst (tsub_inc_above x) (tsubst (tsub_beta_gen 0 t2) t1));
  tsubst_comp (tsub_inc_above x) (tsub_beta_gen 0 t2) t1;
  assert(tshift_up_above x (tsubst_beta t2 t1) =
         tsubst (tsub_comp (tsub_inc_above x) (tsub_beta_gen 0 t2)) t1);

  assert(tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1) =
         tsubst (tsub_beta_gen 0 (tshift_up_above x t2))
                (tshift_up_above (x + 1) t1));
  assert(tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1) =
         tsubst (tsub_beta_gen 0 (tsubst (tsub_inc_above x) t2))
                (tsubst (tsub_inc_above (x+1)) t1));
  tsubst_comp (tsub_beta_gen 0 (tsubst (tsub_inc_above x) t2))
              (tsub_inc_above (x+1)) t1;
  assert(tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1) =
         tsubst (tsub_comp (tsub_beta_gen 0 (tsubst (tsub_inc_above x) t2))
                              (tsub_inc_above (x+1))) t1);
  forall_intro (* #var #(tshift_up_above_tsubst_beta_aux_typ x t2) *)
               (tshift_up_above_tsubst_beta_aux x t2); (* only for speedup *)
  tsubst_extensional (tsub_comp (tsub_inc_above x) (tsub_beta_gen 0 t2))
                     (tsub_comp (tsub_beta_gen 0 (tsubst (tsub_inc_above x) t2))
                                (tsub_inc_above (x+1))) t1

opaque val tequiv_tshift : #t1:typ -> #t2:typ -> h:(tequiv t1 t2) -> x:nat ->
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

val is_var : exp -> Tot(nat)
let is_var e = if is_EVar e then 0 else 1
opaque type renaming (s:esub) = (forall (x:var). is_EVar (s x))

val is_renaming : s:esub -> GTot (n:int{  (renaming s  ==> n=0) /\
                                        (~(renaming s) ==> n=1)})
let is_renaming s = (if excluded_middle (renaming s) then 0 else 1)

type subst_typing (s:esub) (g1:env) (g2:env) =
  f:(x:var{is_Some (lookup_evar g1 x)} ->
     kinding g1 (Some.v (lookup_evar g1 x)) KTyp ->
     Tot(typing g2 (s x) (Some.v (lookup_evar g1 x)))
    ){FEq (MkEnv.a g1) (MkEnv.a g2)}

opaque val substitution :
      #g1:env -> #e:exp -> #t:typ -> s:esub -> #g2:env ->
      h1:typing g1 e t ->
      hs:subst_typing s g1 g2 ->
      Tot (typing g2 (esubst s e) t)
     (decreases %[is_var e; is_renaming s; h1])
let rec substitution g1 e t s g2 h1 hs =
  match h1 with
  | TyVar x kind_normal -> hs x kind_normal
  | TyApp hfun harg -> TyApp (substitution s hfun hs) (substitution s harg hs)
  | TyLam #gtemp tlam #ebody #tfun hkind hbody ->
     let hs'' : subst_typing (esub_inc) (g2) (extend_evar g2 0 tlam) =
       fun x hkind ->
         TyVar (x+1) (kinding_extensional hkind (extend_evar g2 0 tlam)) in
     let hs' : subst_typing (esub_lam s) (extend_evar g1 0 tlam)
                                         (extend_evar g2 0 tlam) =
       fun y hkindg1 ->
         if y = 0
         then TyVar y (kinding_extensional hkindg1 (extend_evar g2 0 tlam))
         else let hgamma2 = hs (y - 1) (kinding_extensional hkindg1 g1) in
              substitution esub_inc hgamma2 hs''
     in (esub_lam_hoist tlam ebody s;
         TyLam tlam (kinding_extensional hkind g2)
               (substitution (esub_lam s) hbody hs'))
  | TyEqu het1 hequiv hkind ->
     TyEqu (substitution s het1 hs) hequiv (kinding_extensional hkind g2)

opaque val typing_substitution: #e:exp -> #v:exp -> #t_x:typ ->
                                #t:typ -> #g:env ->
      h1:(typing g v t_x) ->
      h2:(typing (extend_evar g 0 t_x) e t) ->
      Tot (typing g (esubst_beta v e) t) (decreases %[e;h2])
let rec typing_substitution e v t_x t g h1 h2 =
  let hs : subst_typing (esub_beta v) (extend_evar g 0 t_x) g =
    fun y hkind -> if y = 0 then h1
                   else TyVar (y-1) (kinding_extensional hkind g) in
  substitution (esub_beta v) h2 hs

(* analogous to above *)
val tsubst_gen_tlam_aux : t:typ -> x:var -> y:var ->
      Lemma (tsub_lam (tsub_beta_gen x t) y =
             tsub_beta_gen (x + 1) (tshift_up t) y)
let tsubst_gen_tlam_aux t x y =
  match y with
  | 0 -> ()
  | _ ->
     (assert(tsub_lam (tsub_beta_gen x t) y =
               tsubst tsub_inc (tsub_beta_gen x t (y-1)));
      assert(tsub_beta_gen (x + 1) (tshift_up t) y =
               tsub_beta_gen (x + 1) (tsubst (tsub_inc_above 0) t) y);
      if (y-1) < x then ()
      else if y-1 = x then
        (assert(tsub_lam (tsub_beta_gen x t) y =
                  tsubst tsub_inc t);
         assert(tsub_beta_gen (x + 1) (tshift_up t) y =
                  tsubst (tsub_inc_above 0) t);
         tsubst_extensional tsub_inc (tsub_inc_above 0) t)
      else ())

val tsubst_gen_tlam : x:var -> t:typ -> k:knd -> t':typ -> Lemma
                      (ensures (tsubst_beta_gen x t (TLam k t') =
                       TLam k (tsubst_beta_gen (x + 1) (tshift_up t) t')))
let tsubst_gen_tlam x t k t' =
  assert(tsubst_beta_gen x t (TLam k t') =
           tsubst (tsub_beta_gen x t) (TLam k t'));
  tsub_lam_hoist k t' (tsub_beta_gen x t);
  assert(tsubst_beta_gen x t (TLam k t') =
           TLam k (tsubst (tsub_lam (tsub_beta_gen x t)) t'));

  assert(TLam k (tsubst_beta_gen (x + 1) (tshift_up t) t') =
           TLam k (tsubst (tsub_beta_gen (x + 1) (tshift_up t)) t'));

  forall_intro (tsubst_gen_tlam_aux t x);

  tsubst_extensional (tsub_lam (tsub_beta_gen x t))
                     (tsub_beta_gen (x + 1) (tshift_up t)) t'

(* Parallel type reduction *)

type tred: typ -> typ -> Type =
  | TrRefl: t:typ ->
           tred t t

  | TrArr:  #t1:typ -> #t2:typ -> #t1':typ -> #t2':typ ->
            =hr1:tred t1 t1' ->
            =hr2:tred t2 t2' ->
                 tred (TArr t1 t2) (TArr t1' t2')

  | TrLam:  #t1:typ -> #t2:typ -> k:knd ->
            =hr:tred t1 t2 ->
                tred (TLam k t1) (TLam k t2)

  | TrApp:  #t1:typ -> #t2:typ -> #t1':typ -> #t2':typ ->
            =hr1:tred t1 t1' ->
            =hr2:tred t2 t2' ->
                 tred (TApp t1 t2) (TApp t1' t2')

  | TrBeta: #t1:typ -> #t2:typ -> #t1':typ -> #t2':typ -> k:knd ->
            =hr1:tred t1 t1' ->
            =hr2:tred t2 t2' ->
                 tred (TApp (TLam k t1) t2) (tsubst_beta t2' t1')

(* t => t' implies tshift_up_above x t => tshift_up_above x t' *)
opaque val tred_shiftup_above: #t:typ -> #t':typ -> x:nat -> h:(tred t t') ->
                        Tot (tred (tshift_up_above x t) (tshift_up_above x t'))
                        (decreases h)
let rec tred_shiftup_above t t' x h =
  match h with
    | TrRefl t''  -> TrRefl (tshift_up_above x t'')
    | TrArr h1 h2 -> TrArr (tred_shiftup_above x h1) (tred_shiftup_above x h2)
    | TrLam #t1 #t2 k h1  ->
      tshift_up_above_lam x k t1;
      tshift_up_above_lam x k t2;
      TrLam k (tred_shiftup_above (x + 1) h1)
    | TrApp h1 h2 -> TrApp (tred_shiftup_above x h1) (tred_shiftup_above x h2)
    | TrBeta #t1 #t2 #t1' #t2' k h1 h2 ->
      tshift_up_above_lam x k t1;
      tshift_up_above_tsubst_beta x t1' t2';
      TrBeta k (tred_shiftup_above (x + 1) h1) (tred_shiftup_above x h2)

(* Lemma 30.3.6: s => s' implies t[y |-> s] => t[y |-> s'] *)
opaque val subst_of_tred: #s:typ -> #s':typ -> x:nat -> t:typ ->
                   h:(tred s s') ->
                   Tot (tred (tsubst_beta_gen x s t) (tsubst_beta_gen x s' t))
                   (decreases t)
let rec subst_of_tred s s' x t h =
  match t with
    | TVar y -> if y < x then TrRefl t
                else if y = x then h
                else TrRefl (TVar (y - 1))
    | TLam k t1 ->
      tsubst_gen_tlam x s k t1; tsubst_gen_tlam x s' k t1;
      TrLam k (subst_of_tred (x + 1) t1 (tred_shiftup_above 0 h))
    | TApp t1 t2 ->
      TrApp (subst_of_tred x t1 h) (subst_of_tred x t2 h)
    | TArr t1 t2 ->
      TrArr (subst_of_tred x t1 h) (subst_of_tred x t2 h)

(* short names *)
let ts  = tsubst_beta_gen
let tsh = tshift_up_above

(* shift above and substitute is an identity *)
val shift_above_and_subst: s:typ -> y:nat -> t:typ -> Lemma
                           (ensures (ts y t (tsh y s) = s)) (decreases s)
let rec shift_above_and_subst s y t =
  tsubst_comp (tsub_beta_gen y t) (tsub_inc_above y) s;
  tsubst_extensional (tsub_comp (tsub_beta_gen y t) (tsub_inc_above y)) tsub_id s;
  tsubst_id s

val tsubst_commute_aux : y:nat -> x:nat{x >= y} -> s1:typ -> s2:typ -> v:var ->
      Lemma (requires True)
          (ensures ((tsub_comp (tsub_beta_gen x s1) (tsub_beta_gen y s2)) v =
                    (tsub_comp (tsub_beta_gen y (tsubst_beta_gen x s1 s2))
                               (tsub_beta_gen (x+1) (tshift_up_above y s1))) v))
let tsubst_commute_aux y x s1 s2 v =
  if v = x+1 then shift_above_and_subst s1 y (tsubst_beta_gen x s1 s2)

val tsubst_commute: t1:typ -> y:nat -> t2:typ -> x:nat{x >= y} -> s:typ ->
                    Lemma (requires True)
                    (ensures (ts x s (ts y t2 t1) =
                              ts y (ts x s t2) (ts (x + 1) (tsh y s) t1)))
let rec tsubst_commute t1 y t2 x s =
  tsubst_comp (tsub_beta_gen x s) (tsub_beta_gen y t2) t1;
  forall_intro (tsubst_commute_aux y x s t2);
  tsubst_extensional (tsub_comp (tsub_beta_gen x s) (tsub_beta_gen y t2))
                     (tsub_comp (tsub_beta_gen y (ts x s t2))
                                (tsub_beta_gen (x+1) (tsh y s))) t1;
  tsubst_comp (tsub_beta_gen y (ts x s t2)) (tsub_beta_gen (x+1) (tsh y s)) t1

(* Lemma 30.3.7: t => t' and s => s' implies t[x |-> s] => t'[x |-> s'] *)
opaque val subst_of_tred_tred: #s:typ -> #s':typ -> #t:typ -> #t':typ -> x:nat ->
                       hs:(tred s s') -> ht:(tred t t') ->
                       Tot (tred (tsubst_beta_gen x s t) (tsubst_beta_gen x s' t'))
                       (decreases ht)
let rec subst_of_tred_tred s s' t t' x hs ht =
  match ht with
    | TrRefl t1 -> subst_of_tred x t1 hs
    | TrArr ht1 ht2 ->
      TrArr (subst_of_tred_tred x hs ht1) (subst_of_tred_tred x hs ht2)
    | TrLam #t1 #t2 k ht1 ->
      tsubst_gen_tlam x s k t1;
      tsubst_gen_tlam x s' k t2;
      TrLam k (subst_of_tred_tred (x + 1) (tred_shiftup_above 0 hs) ht1)
    | TrApp h1 h2 ->
      TrApp (subst_of_tred_tred x hs h1) (subst_of_tred_tred x hs h2)
    | TrBeta #t1 #t2 #t1' #t2' k ht1 ht2 ->
      tsubst_gen_tlam x s k t1;
      let ht1' = subst_of_tred_tred (x + 1) (tred_shiftup_above 0 hs) ht1 in
      let ht2' = subst_of_tred_tred x hs ht2 in
      tsubst_commute t1' 0 t2' x s';
      TrBeta k ht1' ht2'

type ltup =
  | MkLTup: #s:typ -> #t:typ -> #u:typ -> =h1:(tred s t) -> =h2:(tred s u) -> ltup

(* single step diamond property of parallel reduction *)
opaque val tred_diamond: #s:typ -> #t:typ -> #u:typ ->
                  h1:(tred s t) -> h2:(tred s u) ->
                  Tot (cexists (fun v -> cand (tred t v) (tred u v)))
                  (decreases %[h1;h2])
let rec tred_diamond s t u h1 h2 =
  match (MkLTup h1 h2) with
    | MkLTup (TrRefl t1) _ -> ExIntro u (Conj h2 (TrRefl u))
    | MkLTup _ (TrRefl t1) -> ExIntro t (Conj (TrRefl t) h1)
    (* if one is TrLam, the other has to be TrLam *)
    | MkLTup (TrLam k h11) (TrLam _ h12) ->
    (* AR: p only has one constructor Conj,
           but direct pattern matching doesn't work *)
      let ExIntro t' (Conj pa pb) = tred_diamond h11 h12 in
      ExIntro (TLam k t') (Conj (TrLam k pa) (TrLam k pb))
    (* if one is TrArr, the other has to be TrArr *)
    | MkLTup (TrArr h11 h12) (TrArr h21 h22) ->
      let ExIntro v1 (Conj p1a p1b) = tred_diamond h11 h21 in
      let ExIntro v2 (Conj p2a p2b) = tred_diamond h12 h22 in
      ExIntro (TArr v1 v2) (Conj (TrArr p1a p2a) (TrArr p1b p2b))
    (* both TrApp *)
    | MkLTup (TrApp h11 h12) (TrApp h21 h22) ->
      let ExIntro v1 (Conj p1a p1b) = tred_diamond h11 h21 in
      let ExIntro v2 (Conj p2a p2b) = tred_diamond h12 h22 in
      ExIntro (TApp v1 v2) (Conj (TrApp p1a p2a) (TrApp p1b p2b))
    (* both TrBeta *)
    | MkLTup (TrBeta #s1 #s2 #t1' #t2' k h11 h12)
             (TrBeta #s11 #s21 #u1' #u2' k' h21 h22) ->
      let ExIntro v1 (Conj p1a p1b) = tred_diamond h11 h21 in
      let ExIntro v2 (Conj p2a p2b) = tred_diamond h12 h22 in
      ExIntro (tsubst_beta v2 v1) (Conj (subst_of_tred_tred 0 p2a p1a)
                                        (subst_of_tred_tred 0 p2b p1b))
    (* one TrBeta and other TrApp *)
    | MkLTup (TrBeta #s1 #s2 #t1' #t2' k h11 h12)
             (TrApp #s1' #s2' #lu1' #u2' h21 h22) ->
    (* AR: does not work without this type annotation *)
      let h21:(tred (TLam.t s1') (TLam.t lu1')) =
        match h21 with
          | TrLam _ h' -> h'
          | TrRefl _ -> TrRefl (TLam.t s1') in
      let ExIntro v1 (Conj p1a p1b) = tred_diamond h11 h21 in
      let ExIntro v2 (Conj p2a p2b) = tred_diamond h12 h22 in
      let v = tsubst_beta v2 v1 in
      ExIntro v (Conj (subst_of_tred_tred 0 p2a p1a) (TrBeta k p1b p2b))

    | MkLTup (TrApp #s1' #s2' #lu1' #u2' h21 h22)
             (TrBeta #s1 #s2 #t1' #t2' k h11 h12) ->
      let ExIntro v1 (Conj p1 p2) = tred_diamond h21 (TrLam k h11) in
      let ExIntro v2 (Conj p3 p4) = tred_diamond h22 h12 in
      let h_body:(tred (TLam.t lu1') (TLam.t v1)) =
        match p1 with
          | TrLam _ h' -> h'
          | TrRefl _ -> TrRefl (TLam.t lu1') in
      let h_body2:(tred t1' (TLam.t v1)) =
        match p2 with
          | TrLam _ h' -> h'
          | TrRefl _ -> TrRefl t1' in
      ExIntro (tsubst_beta v2 (TLam.t v1))
              (Conj (TrBeta k h_body p3) (subst_of_tred_tred 0 p4 h_body2))

type tred_star: typ -> typ -> Type =
  | TsRefl : t:typ ->
             tred_star t t

  | TsStep : #t1:typ -> #t2:typ -> #t3:typ ->
             =hr12:tred      t1 t2 ->
             =hr23:tred_star t2 t3 ->
                   tred_star t1 t3

opaque val tred_star_one_loop: #s:typ -> #t:typ -> #u:typ ->
      h:(tred s t) -> hs:(tred_star s u) ->
      Tot (cexists (fun v -> cand (tred_star t v) (tred u v))) (decreases hs)
let rec tred_star_one_loop s t u h hs = match hs with
  | TsRefl _ ->
    ExIntro t (Conj (TsRefl t) h)
  | TsStep #s #u1 #u h1 hs' ->
    let ExIntro v1 (Conj p1a p1b) = tred_diamond h h1 in
    let ExIntro v (Conj p2a p2b) = tred_star_one_loop p1b hs' in
    ExIntro v (Conj (TsStep p1a p2a) (p2b))

(* aka Church-Rosser; used in Proposition 30.3.10 *)
opaque val confluence : #s:typ -> #t:typ -> #u:typ ->
      h1:(tred_star s t) -> h2:(tred_star s u) ->
      Tot (cexists (fun v -> cand (tred_star t v) (tred_star u v)))
      (decreases h1)
let rec confluence s t u h1 h2 =
  match h1 with
  | TsRefl _ ->
    ExIntro u (Conj h2 (TsRefl u))
  | TsStep #s #t1 #t h1' hs1 ->
     let ExIntro v1 (Conj p1 p2) = tred_star_one_loop h1' h2 in
     let ExIntro v (Conj p1' p2') = confluence hs1 p1 in
     ExIntro v (Conj p1' (TsStep p2 p2'))

opaque val ts_tran: #s:typ -> #t:typ -> #u:typ ->
             h1:tred_star s t -> h2:tred_star t u -> Tot (tred_star s u)
             (decreases h1)
let rec ts_tran s t u h1 h2 =
  match h1 with
    | TsRefl _ -> h2
    | TsStep #s #s1 #t h11 h12 ->
      TsStep h11 (ts_tran h12 h2)

type tred_star_sym : typ -> typ -> Type =
  | TssBase: #t1:typ -> #t2:typ ->
             =hr:tred t1 t2 ->
                 tred_star_sym t1 t2
  | TssSym: #t1:typ -> #t2:typ ->
            =hr:tred_star_sym t2 t1 ->
                tred_star_sym t1 t2
  | TssTran: #t1:typ -> #t2:typ -> #t3:typ ->
             =hr12:tred_star_sym t1 t2 ->
             =hr23:tred_star_sym t2 t3 ->
                   tred_star_sym t1 t3

(* Proposition 30.3.10 in TAPL (has a graphical proof only for this, pg. 561) *)
opaque val tred_star_sym_confluent : #s:typ -> #t:typ ->
      h:tred_star_sym s t ->
      Tot (cexists (fun u -> cand (tred_star s u) (tred_star t u))) (decreases h)
let rec tred_star_sym_confluent s t h =
  match h with
    | TssBase h1 -> ExIntro t (Conj (TsStep h1 (TsRefl t)) (TsRefl t))
    | TssSym h1 ->
      let ExIntro u (Conj p1 p2) = tred_star_sym_confluent h1 in
      ExIntro u (Conj p2 p1)
    | TssTran #s #v #t h1 h2 ->
      let ExIntro u1 (Conj psu1 pvu1) = tred_star_sym_confluent h1 in
      let ExIntro u2 (Conj pvu2 ptu2) = tred_star_sym_confluent h2 in
      let ExIntro w (Conj pu1w pu2w) = confluence pvu1 pvu2 in
      ExIntro w (Conj (ts_tran psu1 pu1w) (ts_tran ptu2 pu2w))

opaque val trlam_tss : #t1:typ -> #t2:typ -> k:knd ->
      h:(tred_star_sym t1 t2) ->
      Tot (tred_star_sym (TLam k t1) (TLam k t2)) (decreases h)
let rec trlam_tss t1 t2 k h =
  match h with
    | TssBase h1 -> TssBase (TrLam k h1)
    | TssSym h1 -> TssSym (trlam_tss k h1)
    | TssTran h1 h2 -> TssTran (trlam_tss k h1) (trlam_tss k h2)

opaque val trapp_tss_1 : #t1:typ -> t2:typ -> #t1':typ ->
      h:(tred_star_sym t1 t1') ->
      Tot (tred_star_sym (TApp t1 t2) (TApp t1' t2)) (decreases h)
let rec trapp_tss_1 t1 t2 t1' h =
  match h with
    | TssBase h1 -> TssBase (TrApp h1 (TrRefl t2))
    | TssSym h1 -> TssSym (trapp_tss_1 t2 h1)
    | TssTran h1 h2 -> TssTran (trapp_tss_1 t2 h1) (trapp_tss_1 t2 h2)

opaque val trapp_tss_2 : t1:typ -> #t2:typ -> #t2':typ ->
      h:(tred_star_sym t2 t2') ->
      Tot (tred_star_sym (TApp t1 t2) (TApp t1 t2')) (decreases h)
let rec trapp_tss_2 t1 t2 t2' h =
  match h with
    | TssBase h1 -> TssBase (TrApp (TrRefl t1) h1)
    | TssSym h1 -> TssSym (trapp_tss_2 t1 h1)
    | TssTran h1 h2 -> TssTran (trapp_tss_2 t1 h1) (trapp_tss_2 t1 h2)

(* copy paste from above *)
opaque val trarr_tss_1 : #t1:typ -> t2:typ -> #t1':typ ->
      h:(tred_star_sym t1 t1') ->
      Tot (tred_star_sym (TArr t1 t2) (TArr t1' t2)) (decreases h)
let rec trarr_tss_1 t1 t2 t1' h =
  match h with
    | TssBase h1 -> TssBase (TrArr h1 (TrRefl t2))
    | TssSym h1 -> TssSym (trarr_tss_1 t2 h1)
    | TssTran h1 h2 -> TssTran (trarr_tss_1 t2 h1) (trarr_tss_1 t2 h2)

opaque val trarr_tss_2 : t1:typ -> #t2:typ -> #t2':typ ->
      h:(tred_star_sym t2 t2') ->
      Tot (tred_star_sym (TArr t1 t2) (TArr t1 t2')) (decreases h)
let rec trarr_tss_2 t1 t2 t2' h =
  match h with
    | TssBase h1 -> TssBase (TrArr (TrRefl t1) h1)
    | TssSym h1 -> TssSym (trarr_tss_2 t1 h1)
    | TssTran h1 h2 -> TssTran (trarr_tss_2 t1 h1) (trarr_tss_2 t1 h2)

(* LTR direction of Lemma 30.3.5 in TAPL; proof there is informal and unclear. *)
opaque val tequiv_tss : #s:typ -> #t:typ -> h:(tequiv s t) ->
      Tot (tred_star_sym s t) (decreases h)
let rec tequiv_tss s t h =
  match h with
  | EqRefl _ -> TssBase (TrRefl s)
  | EqSymm h1 -> TssSym (tequiv_tss h1)
  | EqTran h1 h2 -> TssTran (tequiv_tss h1) (tequiv_tss h2)
  | EqLam #t #t' k h1 -> TssTran (trlam_tss k (tequiv_tss h1))
                                 (TssBase (TrRefl (TLam k t')))
  | EqBeta k t1' t2' -> TssBase (TrBeta k (TrRefl t1') (TrRefl t2'))
  | EqApp #t1 #t1' #t2 #t2' h1 h2 ->
    TssTran (trapp_tss_1 t2  (tequiv_tss h1))
            (trapp_tss_2 t1' (tequiv_tss h2))
  | EqArr #t1 #t1' #t2 #t2' h1 h2 ->
     TssTran (trarr_tss_1 t2  (tequiv_tss h1))
             (trarr_tss_2 t1' (tequiv_tss h2))

(* Corrolary 30.3.11 in TAPL. Used in inversion_elam. *)
opaque val tequiv_tred_tred : #s:typ -> #t:typ ->
      tequiv s t ->
      Tot (cexists (fun u -> cand (tred_star s u) (tred_star t u)))
let tequiv_tred_tred s t h = tred_star_sym_confluent (tequiv_tss h)

opaque val tred_tequiv : #s:typ -> #t:typ -> h:(tred s t) ->
                  Tot (tequiv s t) (decreases h)
let rec tred_tequiv s t h =
  match h with
  | TrRefl _ -> EqRefl s
  | TrArr h1 h2 -> EqArr (tred_tequiv h1) (tred_tequiv h2)
  | TrLam k h1 -> EqLam k (tred_tequiv h1)
  | TrApp h1 h2 -> EqApp (tred_tequiv h1) (tred_tequiv h2)
  | TrBeta #t1 #t2 #t1' #t2' k h1 h2 ->
     EqTran (EqApp (EqLam k (tred_tequiv h1)) (tred_tequiv h2))
            (EqBeta k t1' t2')

opaque val tred_star_tequiv : #s:typ -> #t:typ -> h:(tred_star s t) ->
                       Tot (tequiv s t) (decreases h)
let rec tred_star_tequiv s t h = match h with
  | TsRefl _ -> EqRefl s
  | TsStep h1 h2 -> EqTran (tred_tequiv h1) (tred_star_tequiv h2)

(* RTL direction of Lemma 30.3.5 in TAPL. TAPL calls this direction obvious.
   We don't use this anywhere *)
opaque val tss_tequiv : #s:typ -> #t:typ ->
      h:(tred_star_sym s t) -> Tot (tequiv s t) (decreases h)
let rec tss_tequiv s t h =
  match h with
    | TssBase h1 -> tred_tequiv h1
    | TssSym h1 -> EqSymm (tss_tequiv h1)
    | TssTran h1 h2 -> EqTran (tss_tequiv h1) (tss_tequiv h2)

#set-options "--initial_ifuel 2 --max_ifuel 2"
opaque val tred_tarr_preserved : #s1:typ -> #s2:typ -> #t:typ ->
      h:(tred_star (TArr s1 s2) t) ->
      Tot (cexists (fun t1 -> (cexists (fun t2 ->
            (u:(cand (tred_star s1 t1) (tred_star s2 t2)){t = TArr t1 t2})))))
      (decreases h)
let rec tred_tarr_preserved s1 s2 t h =
  match h with
    | TsRefl _ -> ExIntro s1 (ExIntro s2 (Conj (TsRefl s1) (TsRefl s2)))
    | TsStep #s #u #t h1 hs1 ->
      match h1 with
          | TrRefl _ -> tred_tarr_preserved hs1
          | TrArr #s1 #s2 #u1 #u2 h11 h12 ->
            (* AR: does not work without specifying implicits *)
            let ExIntro t1 (ExIntro t2 (Conj p1 p2)) =
                                           tred_tarr_preserved #u1 #u2 #t hs1 in
            ExIntro t1 (ExIntro t2 (Conj (TsStep h11 p1) (TsStep h12 p2)))
//NS: Something seems super fragile here ...
opaque val inversion_elam :
      #g:env -> s1:typ -> e:exp -> #s:typ -> t1:typ -> t2:typ ->
      ht:typing g (ELam s1 e) s -> heq:tequiv s (TArr t1 t2) ->
      hnew:kinding g t2 KTyp ->
      Tot (cand (cand (tequiv t1 s1) (typing (extend_evar g 0 s1) e t2))
                (kinding g s1 KTyp))  (decreases ht)
let rec inversion_elam g s1 e s t1 t2 ht heq hnew = match ht with
  | TyEqu #g #e' #u #s ht1 heq1 k1 ->
    inversion_elam s1 e t1 t2 ht1 (EqTran heq1 heq) hnew
  | TyLam #g s1 #e #s2 hk ht1 ->
    let ExIntro u p = tequiv_tred_tred heq in
    let Conj p1 p2 = p in
    (* NS:
       p1:tred_star (TArr s1 s2) u
       p2:tred_star (TArr t1 t2) u
    *)

    (* AR: implicits required *)
    (*let ExIntro u1 pp = tred_tarr_preserved #s1 #s2 #u p1 in
    let ExIntro u2 (Conj psu1 psu2) = pp in
    *)
    let ExIntro u1 (ExIntro u2 (Conj psu1 psu2)) = tred_tarr_preserved #s1 #s2 #u p1 in
    (* NS:
       psu1: tred_star (TArr s1 s2) (TArr u1 u2)
       psu2: tred_star u (TArr u1 u2)
    *)

    (* AR: implicits required *)
    (* CH: can't merge these two matches (error: "Patterns are incomplete") *)
    let ExIntro u1' p = tred_tarr_preserved #t1 #t2 #u p2 in
    let ExIntro u2' (Conj ptu1 ptu2) = p in
    (* NS:
        ptu1: tred_star (TArr s1 s2) (TArr u1' u2')
        ptu2: tred_star u (TArr u1' u2')
    *)

    (*
     * AR: so now we have tequiv s2 t2, and ht1. as TAPL says, we now want to use
     * TyEqu to derive typing judgment with result type t2 (ht1 has result type s2).
     * but, TyEqu also requires that g |- t2 :: KTyp, which means we are stuck.
     * i don't see a way to derive this kinding judgment just given the premises.
     *
     * i am fixing it by making sure that all typing judgments result in types
     * that have kind KTyp. so then, we can derive s2::KTyp, and since tequiv s2 t2,
     * we will get t2::KTyp. to do so, i had to make a small change to TyVar
     * requiring that the lookup type has kind KTyp.
     *)

    let pst2 = EqTran (tred_star_tequiv psu2) //NS: tequiv (TArr u1 u2) u
                      (EqSymm (tred_star_tequiv ptu2))  //NS: tequiv u (TArr u1' u2')
                      in
    let h:(typing (extend_evar g 0 s1) e t2) =
      TyEqu ht1 pst2 (kinding_weakening_ebnd hnew 0 s1) in
    Conj (Conj (EqTran (tred_star_tequiv ptu1)
                       (EqSymm (tred_star_tequiv psu1))) h) hk
#reset-options

(* Corollary of inversion_elam *)
opaque val inversion_elam_typing : #g:env -> s1:typ -> e:exp ->
      t1:typ -> t2:typ -> typing g (ELam s1 e) (TArr t1 t2) ->
      Tot (cand (cand (tequiv t1 s1) (typing (extend_evar g 0 s1) e t2))
                (kinding g s1 KTyp))
let inversion_elam_typing g s1 e t1 t2 h =
  inversion_elam s1 e t1 t2 h (EqRefl (TArr t1 t2))
    (Conj.h2 (kinding_inversion_arrow #g #t1 #t2 (typing_to_kinding h)))

(* Type preservation *)
opaque val preservation : #e:exp -> #e':exp -> hs:step e e' ->
                   #g:env -> #t:typ -> ht:(typing g e t) ->
                   Tot (typing g e' t) (decreases ht)
let rec preservation _ _ hs _ _ ht =
  match ht with
  | TyApp #g #e1 #e2 #t1 #t2 h1 h2 ->
    (match hs with
     | SBeta s1 e11 e12 ->
       let Conj (Conj p1 p2) p3 = inversion_elam_typing s1 e11 t1 t2 h1 in
       typing_substitution (TyEqu h2 p1 p3) p2
     | SApp1 e2' hs1   -> TyApp (preservation hs1 h1) h2
     | SApp2 e1' hs2   -> TyApp h1 (preservation hs2 h2))
  | TyEqu ht1 he hk -> TyEqu (preservation hs ht1) he hk
