(*--build-config
    options:--admit_fsi FStar.Set --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1;
    other-files:FStar.Constructive.fst FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
 --*)
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

module FOmega

open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality

(* System F omega *)

type var = nat

type knd =
  | KTyp : knd
  | KArr : knd -> knd -> knd

type typ =
  | TVar : var -> typ
  | TLam : knd -> t:typ -> typ
  | TApp : typ -> typ -> typ
  | TArr : typ -> typ -> typ

  | TFor : knd -> typ -> typ

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | ELam   : typ -> exp -> exp

  | EForT  : knd -> exp -> exp
  | ETApp  : exp -> typ -> exp

(* Substitution on expressions
   (in this calculus doesn't interact with type substitution below) *)

type esub = var -> Tot exp
type erenaming (s:esub) = (forall (x:var). is_EVar (s x))

val is_erenaming : s:esub -> GTot (n:int{(  erenaming s  ==> n=0) /\
                                         (~(erenaming s) ==> n=1)})
let is_erenaming s = (if excluded_middle (erenaming s) then 0 else 1)

val esub_inc : var -> Tot exp
let esub_inc y = EVar (y+1)

val erenaming_sub_inc : unit -> Lemma (erenaming (esub_inc))
let erenaming_sub_inc _ = ()

let is_evar (e:exp) : int = if is_EVar e then 0 else 1

type tsub = var -> Tot typ
opaque type trenaming (s:tsub) = (forall (x:var). is_TVar (s x))

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

val tsubst : t:typ -> s:tsub -> Pure typ (requires True)
      (ensures (fun t' -> trenaming s /\ is_TVar t ==> is_TVar t'))
      (decreases %[is_tvar t; is_trenaming s; t])

let rec tsubst t s =
  match t with
  | TVar x -> s x

  | TFor k t1
  | TLam k t1 ->
     let tsubst_lam : y:var -> Tot (t:typ{trenaming s ==> is_TVar t}) = fun y ->
       if y=0
       then TVar y
       else (tsubst (s (y - 1)) tsub_inc) in
     TLam k (tsubst t1 tsubst_lam)

  | TArr t1 t2 -> TArr (tsubst t1 s) (tsubst t2 s)
  | TApp t1 t2 -> TApp (tsubst t1 s) (tsubst t2 s)


val esubst_t : e:exp -> st:tsub -> Tot exp
let rec esubst_t e st =
  match e with
    | EVar _ -> e
    | EApp e1 e2 -> EApp (esubst_t e1 st) (esubst_t e2 st)
    | ELam t e1 -> ELam (tsubst t st) (esubst_t e1 st)
    | EForT k e1 ->
      let esubst_tlam : ty:var -> Tot typ = fun ty ->
	if ty = 0 then TVar ty
	else tsubst (st (ty - 1)) tsub_inc
      in
      EForT k (esubst_t e1 esubst_tlam)
    | ETApp e1 t -> ETApp (esubst_t e1 st) (tsubst t st)


val esubst : e:exp -> s:esub -> Pure exp (requires True)
      (ensures (fun e' -> erenaming s /\ is_EVar e ==> is_EVar e'))
      (decreases %[is_evar e; is_erenaming s; e])

let rec esubst e s =
  match e with
  | EVar x -> s x

  | ELam t e1 ->
     let esubst_lam : y:var -> Tot (e:exp{erenaming s ==> is_EVar e}) = fun y ->
       if y=0 then EVar y
       else (esubst (s (y - 1)) esub_inc) in
     ELam t (esubst e1 esubst_lam)

  | EForT k e1 -> EForT k (esubst e1 (fun y -> esubst_t (s y) tsub_inc))

  | ETApp e1 t -> ETApp (esubst e1 s) t

  | EApp e1 e2 -> EApp (esubst e1 s) (esubst e2 s)

val esubst_lam: s:esub -> Tot esub
let esubst_lam s y =
  if y = 0 then EVar y
  else esubst (s (y-1)) esub_inc

(* val esubst_lam_renaming: s:esub -> Lemma *)
(*   (ensures (forall (x:var). erenaming s ==> is_EVar (esubst_lam s x))) *)
(* let esubst_lam_renaming s = () *)

(* Substitution extensional; trivial with the extensionality axiom *)
val esubst_extensional: s1:esub -> s2:esub{FEq s1 s2} -> e:exp ->
                        Lemma (requires True) (ensures (esubst e s1 = esubst e s2))
                       (* [SMTPat (esubst e s1);  SMTPat (esubst e s2)] *)
let esubst_extensional s1 s2 e = ()

val esubst_textensional: s1:tsub -> s2:tsub{FEq s1 s2} -> e:exp ->
                         Lemma (requires True) (ensures (esubst_t e s1 = esubst_t e s2))
let esubst_textensional s1 s2 e = ()

(* This only works automatically with the patterns in subst_extensional above;
   it would be a lot cooler if this worked without, since that increases checking time.
   Even worse, there is no way to prove this without the SMTPat (e.g. manually),
   or to use the SMTPat only locally, in this definition (`using` needed). *)
val esubst_lam_hoist : t:typ -> e:exp -> s:esub -> Lemma (requires True)
      (ensures (esubst (ELam t e) s = ELam t (esubst e (esubst_lam s))))
      (* [SMTPat (esubst (ELam t e) s)] (\* -- even this increases running time by 10 secs *\) *)
let esubst_lam_hoist t e s = admit()

(* (\* Substitution composition *\) *)

(* val esub_comp : s1:esub -> s2:esub -> Tot esub *)
(* let esub_comp s1 s2 x = esubst (s2 x) s1 *)

(* type esub_comp_inc_type (s:esub) (x:var) = *)
(*   (esub_comp esub_inc s x = esub_comp (esubst_lam s) esub_inc x) *)

(* val esub_comp_inc : s:esub -> x:var -> Lemma (esub_comp_inc_type s x) *)
(* let esub_comp_inc s x = *)
(*   assert(esub_comp esub_inc s x = esubst (s x) esub_inc); *)
(*   assert(esub_comp (esubst_lam s) esub_inc x = *)
(*                                   esubst (EVar (x+1)) (esubst_lam s)); *)
(*   assert(esub_comp (esubst_lam s) esub_inc x = esubst_lam s (x+1)); *)
(*   assert(esub_comp (esubst_lam s) esub_inc x = esubst (s x) esub_inc) *)

(* type esubst_lam_composes (s1:esub) (s2:esub) (x:var) = *)
(*   (esubst_lam (esub_comp s1 s2) x = esub_comp (esubst_lam s1) (esubst_lam s2) x) *)

(* val esubst_comp : s1:esub -> s2:esub -> e:exp -> Lemma *)
(*       (ensures (esubst (esubst e s2) s1 = esubst e (esub_comp s1 s2))) *)
(*       (decreases %[is_evar e; *)
(*                    is_erenaming s1; *)
(*                    is_erenaming s2; *)
(*                    e]) *)
(* let rec esubst_comp s1 s2 e = *)
(*   match e with *)
(*   | EVar x -> () *)
(*   | EApp e1 e2 -> *)
(*     esubst_comp s1 s2 e1; *)
(*     esubst_comp s1 s2 e2 *)

(*   | ELam t e1 -> *)
(*     (\* Sketch of the proof: *)
(*                esubst (esubst (ELam t e1) s2) s1 *)
(*   def,hoist1=  esubst (ELam t (esubst e1 (esubst_lam s2)) s1 *)
(*   def,hoist2=  ELam t (esubst (esubst e1 (esubst_lam s2)) (esubst_lam s1)) *)
(*           h1=  ELam t (esubst e1 (esub_comp (esubst_lam s1) (esubst_lam s2))) *)
(*       h2,ext=  ELam t (esubst e1 (esubst_lam (esub_comp s1 s2)) *)
(*   def,hoist3=  esubst (ELam t e1) (esubst_comp s1 s2) *)
(*     *\) *)

(*     let esubst_lam_comp : x:var -> Lemma *)
(*       (esubst_lam_composes s1 s2 x) = fun x -> *)
(*         match x with *)
(*           | 0 -> () *)
(*           | _ -> *)
(*             (\* sketch: *)
(*                      esubst_lam (esub_comp s1 s2) x *)
(*            def=      esubst (esub_comp s1 s2 (x-1)) esub_inc *)
(*            def=      esubst (esubst (s2 (x - 1)) s1) esub_inc *)
(*            ih1=      esubst (s2 (x-1)) (esub_comp esub_inc s1) *)
(* esub_comp_inc,ext=   esubst (s2 (x-1)) (esub_comp (esubst_lam s1) esub_inc) *)
(*            ih2=      esubst (esubst (s2 (x-1)) esub_inc) (esubst_lam s1) *)
(*            def=      esubst (esubst_lam s2 x) (esubst_lam s1) *)
(*               =      esub_comp (esubst_lam s1) (esubst_lam s2) x *)
(*             *\) *)
(*             begin *)
(*             (\* terminates because: *)
(*                1. if s2 is a renaming, then s2 (x - 1) is a var and e is a non-var *)
(*                2. else if s1 is a renaming, then esub_inc is a renaming so *)
(*                both the first and 2nd components remain the same; *)
(*                but the third component goes down (s1 is a renaming and s2 is not). *)
(*                3. else the second component goes down since esub_inc is a *)
(*                   renaming and s1 is not. *\) *)

(*               let ih1 = *)
(*                 erenaming_sub_inc (); *)
(*                 esubst_comp esub_inc s1 (s2 (x-1)) in *)

(*               let ext = *)
(*                 forall_intro (\* #var #(esub_comp_inc_type s1) *\) (esub_comp_inc s1); *)
(*                 esubst_extensional *)
(*                   (esub_comp esub_inc s1) *)
(*                   (esub_comp (esubst_lam s1) esub_inc) (s2 (x-1)) in *)

(*             (\* terminates because: *)
(*                1. if s2 is a renaming ... easy. *)
(*                2. else if s1 is a renaming, (esubst_lam s1) is a renaming, *)
(*                   and the third component goes down. *)
(*                3. else the third component goes down. *\) *)
(*               let ih2 = *)
(*                 esubst_lam_renaming s1; *)
(*                 erenaming_sub_inc (); *)
(*                 esubst_comp (esubst_lam s1) esub_inc (s2 (x-1)) in *)

(*               () *)

(*             end in *)


(*     let hoist1 = esubst_lam_hoist t e1 s2 in *)
(*     let hoist2 = esubst_lam_hoist t (esubst e1 (esubst_lam s2)) s1 in *)


(*     (\* terminates because e1 is a sub-term, *)
(*        and (esubst_lam s1/s2) are renamings if s1/s2 are. *)
(*        h1 proves   esubst (esubst e1 (esubst_lam s2)) (esubst_lam s1) *)
(*                  = esubst e1 (esub_comp (esubst_lam s1) (esubst_lam s2)) *)
(*     *\) *)
(*     let h1 = *)
(*       esubst_lam_renaming s1; *)
(*       esubst_lam_renaming s2; *)
(*       esubst_comp (esubst_lam s1) (esubst_lam s2) e1 in *)

(*     let h2 = *)
(*       forall_intro (\* #var #(esubst_lam_composes s1 s2) *\) esubst_lam_comp; *)
(*       cut (FEq (esub_comp (esubst_lam s1) (esubst_lam s2)) *)
(*              (esubst_lam (esub_comp s1 s2))) in *)

(*     let ext = esubst_extensional *)
(*       (esub_comp (esubst_lam s1) (esubst_lam s2)) *)
(*       (esubst_lam (esub_comp s1 s2)) *)
(*       e1 in *)

(*     let hoist3 = esubst_lam_hoist t e1 (esub_comp s1 s2) in *)
(*     () *)

(* (\* Identity substitution *\) *)

val esub_id : esub
let esub_id x = EVar x

(* AR: struggled with this for a long time *)
val esubst_forallt: s:esub -> Tot esub
let esubst_forallt s y = esubst_t (s y) tsub_inc

val esubst_forallt_hoist : k:knd -> e:exp -> s:esub -> Lemma (requires True)
      (ensures (esubst (EForT k e) s = EForT k (esubst e (esubst_forallt s))))
let esubst_forallt_hoist k e s = admit()

val esubst_id : e:exp -> Lemma (esubst e esub_id = e)
let rec esubst_id e =
  match e with
    | EVar _ -> ()
    | ELam t e1 ->
      esubst_lam_hoist t e1 esub_id;
      esubst_extensional esub_id (esubst_lam esub_id) e1;
      esubst_id e1
    | EApp e1 e2 -> esubst_id e1; esubst_id e2

    | EForT k e1 ->
      esubst_forallt_hoist k e1 esub_id;
      esubst_extensional esub_id (esubst_forallt esub_id) e1;
      esubst_id e1

    | ETApp e1 t -> esubst_id e1

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

val tsubst_lam: s:tsub -> Tot tsub
let tsubst_lam s y =
  if y = 0 then TVar y
  else tsubst (s (y-1)) tsub_inc

(* Type substitution extensional; trivial with the extensionality axiom *)
val tsubst_extensional: s1:tsub -> s2:tsub{FEq s1 s2} -> t:typ ->
                        Lemma (requires True) (ensures (tsubst t s1 = tsubst t s2))
(*                       [SMTPat (tsubst t s1);  SMTPat (tsubst t s2)]*)
let tsubst_extensional s1 s2 t = ()

(* Same silly situation as for esubst_lam_hoist *)
val tsubst_lam_hoist : k:knd -> t:typ -> s:tsub -> Lemma
      (ensures (tsubst (TLam k t) s = TLam k (tsubst t (tsubst_lam s)) /\
                tsubst (TFor k t) s = TFor k (tsubst t (tsubst_lam s))))
let tsubst_lam_hoist k t s = admit()

let esubst_tforall = tsubst_lam

val esubst_tforall_hoist: k:knd -> e:exp -> t:tsub -> Lemma (requires True)
                          (ensures (esubst_t (EForT k e) t = EForT k (esubst_t e (esubst_tforall t))))
let esubst_tforall_hoist k e t = admit ()

(* Type substitution composition (again analogous) *)

val tsub_comp : s1:tsub -> s2:tsub -> Tot tsub
let tsub_comp s1 s2 x = tsubst (s2 x) s1

(* CH: admitting these for now, they are exactly the same as for esubst *)
assume val tsubst_comp : s1:tsub -> s2:tsub -> t:typ -> Lemma
      (tsubst (tsubst t s2) s1 = tsubst t (tsub_comp s1 s2))

(* Identity substitution *)

val tsub_id : tsub
let tsub_id x = TVar x

val tsubst_id : t:typ -> Lemma (tsubst t tsub_id = t)
let rec tsubst_id t =
  match t with
    | TVar z -> ()
    | TFor k t1
    | TLam k t1 ->
      tsubst_lam_hoist k t1 tsub_id;
      tsubst_extensional tsub_id (tsubst_lam tsub_id) t1;
      tsubst_id t1
    | TArr t1 t2
    | TApp t1 t2 -> tsubst_id t1; tsubst_id t2

(* Beta *)

val tsub_beta_gen : var -> typ -> Tot tsub
let tsub_beta_gen x t = fun y -> if y < x then (TVar y)
                                 else if y = x then t
                                 else (TVar (y-1))

val tsubst_beta_gen : var -> typ -> typ -> Tot typ
let tsubst_beta_gen x t' t = tsubst t (tsub_beta_gen x t')

let tsubst_beta t' t = tsubst_beta_gen 0 t' t

val esubst_tbeta_gen : var -> typ -> exp -> Tot exp
let esubst_tbeta_gen tx t e = esubst_t e (tsub_beta_gen tx t)

val esubst_tbeta : typ -> exp -> Tot exp
let esubst_tbeta t e = esubst_tbeta_gen 0 t e

(* Shifting *)

val tshift_up_above : nat -> typ -> Tot typ
let tshift_up_above x t = tsubst t (tsub_inc_above x)

val tshift_up : typ -> Tot typ
let tshift_up = tshift_up_above 0

val tshift_up_above_e: x:nat -> e:exp -> Tot exp (decreases e)
let rec tshift_up_above_e x e = esubst_t e (tsub_inc_above x)

val tshift_up_above_lam: n:nat -> k:knd -> t:typ -> Lemma
  (ensures (tshift_up_above n (TLam k t) = TLam k (tshift_up_above (n + 1) t) /\
            tshift_up_above n (TFor k t) = TFor k (tshift_up_above (n + 1) t)))
let tshift_up_above_lam n k t =
  assert(tshift_up_above n (TLam k t) = tsubst (TLam k t) (tsub_inc_above n));
  assert(tshift_up_above n (TFor k t) = tsubst (TFor k t) (tsub_inc_above n));
  tsubst_lam_hoist k t (tsub_inc_above n);
  assert(tshift_up_above n (TLam k t) =
         TLam k (tsubst t (tsubst_lam (tsub_inc_above n))));
  assert(tshift_up_above n (TFor k t) =
         TFor k (tsubst t (tsubst_lam (tsub_inc_above n))));
  tsubst_extensional (tsubst_lam (tsub_inc_above n)) (tsub_inc_above (n+1)) t

(* analogous to above *)
type tsubst_gen_tlam_aux_type (t:typ) (x:var) (y:var) =
  (tsubst_lam (tsub_beta_gen x t) y = tsub_beta_gen (x + 1) (tshift_up t) y)
val tsubst_gen_tlam_aux : t:typ -> x:var -> y:var ->
      Lemma (tsubst_gen_tlam_aux_type t x y)
let tsubst_gen_tlam_aux t x y =
  match y with
    | 0 -> ()
    | _ ->
      (assert(tsubst_lam (tsub_beta_gen x t) y =
          tsubst (tsub_beta_gen x t (y-1)) tsub_inc);
       assert(tsub_beta_gen (x + 1) (tshift_up t) y =
           tsub_beta_gen (x + 1) (tsubst t (tsub_inc_above 0)) y);
       if (y-1) < x then ()
       else if y-1 = x then
         (assert(tsubst_lam (tsub_beta_gen x t) y =
             tsubst t tsub_inc);
          assert(tsub_beta_gen (x + 1) (tshift_up t) y =
              tsubst t (tsub_inc_above 0));
          tsubst_extensional tsub_inc (tsub_inc_above 0) t)
       else ())

val tsubst_gen_tlam : x:var -> t:typ -> k:knd -> t':typ -> Lemma
                      (ensures (tsubst_beta_gen x t (TLam k t') =
                       TLam k (tsubst_beta_gen (x + 1) (tshift_up t) t') /\
			        tsubst_beta_gen x t (TFor k t') =
                       TFor k (tsubst_beta_gen (x + 1) (tshift_up t) t')))
let tsubst_gen_tlam x t k t' =
  assert(tsubst_beta_gen x t (TLam k t') =
           tsubst (TLam k t') (tsub_beta_gen x t));
  assert(tsubst_beta_gen x t (TFor k t') =
           tsubst (TFor k t') (tsub_beta_gen x t));
  tsubst_lam_hoist k t' (tsub_beta_gen x t);
  assert(tsubst_beta_gen x t (TLam k t') =
           TLam k (tsubst t' (tsubst_lam (tsub_beta_gen x t))));
  assert(tsubst_beta_gen x t (TFor k t') =
           TFor k (tsubst t' (tsubst_lam (tsub_beta_gen x t))));

  assert(TLam k (tsubst_beta_gen (x + 1) (tshift_up t) t') =
           TLam k (tsubst t' (tsub_beta_gen (x + 1) (tshift_up t))));
  assert(TFor k (tsubst_beta_gen (x + 1) (tshift_up t) t') =
           TFor k (tsubst t' (tsub_beta_gen (x + 1) (tshift_up t))));

  forall_intro (* #var #(tsubst_gen_tlam_aux_type t x) *) (tsubst_gen_tlam_aux t x);

  tsubst_extensional (tsubst_lam (tsub_beta_gen x t))
                     (tsub_beta_gen (x + 1) (tshift_up t)) t'

(* short names *)
let ts  = tsubst_beta_gen
let tsh = tshift_up_above
let tshe = tshift_up_above_e

(* reordering shifts *)
(* CH: there might be a nicer proof for this using substitution composition *)
val tshifts_reordering: x:nat -> y:nat{y >= x} -> s:typ -> Lemma (requires True)
                        (ensures (tsh x (tsh y s) = tsh (y + 1) (tsh x s)))
             	        (decreases s)
let rec tshifts_reordering x y s =
  match s with
    | TVar z -> ()
    | TFor k t1'
    | TLam k t1' ->
      tshift_up_above_lam y k t1';
      tshift_up_above_lam x k (tsh (y + 1) t1');
      tshifts_reordering (x + 1) (y + 1) t1';
      tshift_up_above_lam x k t1';
      tshift_up_above_lam (y + 1) k (tsh (x + 1) t1')
    | TArr t1' t2'
    | TApp t1' t2' -> tshifts_reordering x y t1'; tshifts_reordering x y t2'

val tsubst_commute_helper: x:nat -> y:nat{x >= y} ->s:typ -> t:typ ->
          Lemma (requires True)
                (ensures (tsh y (ts x s t) = ts (x + 1) (tsh y s) (tsh y t)))
         (decreases t)
let rec tsubst_commute_helper x y s t =
  match t with
    | TVar z -> ()
    | TFor k t1'
    | TLam k t1' ->
      tsubst_gen_tlam x s k t1';
      tshift_up_above_lam y k (ts (x + 1) (tsh 0 s) t1');
      tsubst_commute_helper (x + 1) (y + 1) (tsh 0 s) t1';
      tshift_up_above_lam y k t1';
      tsubst_gen_tlam (x + 1) (tsh y s) k (tsh (y + 1) t1');
      tshifts_reordering 0 y s
    | TArr t1' t2'
    | TApp t1' t2' -> tsubst_commute_helper x y s t1'; tsubst_commute_helper x y s t2'

(* shift above and substitute is an identity *)
val shift_above_and_subst: s:typ -> y:nat -> t:typ -> Lemma (requires True)
                           (ensures (ts y t (tsh y s) = s)) (decreases s)
let rec shift_above_and_subst s y t =
  tsubst_comp (tsub_beta_gen y t) (tsub_inc_above y) s;
  tsubst_extensional (tsub_comp (tsub_beta_gen y t) (tsub_inc_above y)) tsub_id s;
  tsubst_id s

val tsubst_commute: t1:typ -> y:nat -> t2:typ -> x:nat{x >= y} -> s:typ ->
                    Lemma (requires True)
		    (ensures (ts x s (ts y t2 t1) =
                              ts y (ts x s t2) (ts (x + 1) (tsh y s) t1)))
                    (decreases t1)
let rec tsubst_commute t1 y t2 x s =
  match t1 with
    | TVar z ->
      if z > y && z = x + 1 then
    	shift_above_and_subst s y (ts x s t2)
      else
    	()
    | TFor k t1'
    | TLam k t1' ->
      tsubst_gen_tlam y t2 k t1';
      tsubst_gen_tlam x s k (ts (y + 1) (tsh 0 t2) t1');
      tsubst_commute t1' (y + 1) (tsh 0 t2) (x + 1) (tsh 0 s);
      tsubst_gen_tlam (x + 1) (tsh y s) k t1';
      tsubst_gen_tlam y (ts x s t2) k (ts (x + 2) (tsh 0 (tsh y s)) t1');
      tsubst_commute_helper x 0 s t2;
      tshifts_reordering 0 y s
    | TArr t1' t2'
    | TApp t1' t2' -> tsubst_commute t1' y t2 x s; tsubst_commute t2' y t2 x s

val tsubst_commute2: y:nat -> x:nat {x >= y} -> t1:typ -> t2:typ -> Lemma (requires True)
                     (ensures (ts y (tsh x t1) (tsh (x + 1) t2) =
                               tsh x (ts y t1 t2)))
                     (decreases t2)
let rec tsubst_commute2 y x t1 t2 =
  match t2 with
    | TVar z -> ()
    | TFor k t2'
    | TLam k t2' ->
      tshift_up_above_lam (x + 1) k t2';
      tsubst_gen_tlam y (tsh x t1) k (tsh (x + 2) t2');
      tsubst_gen_tlam y t1 k t2';
      tshift_up_above_lam x k (ts (y + 1) (tsh 0 t1) t2');
      tsubst_commute2 (y + 1) (x + 1) (tsh 0 t1) t2';
      tshifts_reordering 0 x t1
    | TApp t3 t4
    | TArr t3 t4 -> tsubst_commute2 y x t1 t3; tsubst_commute2 y x t1 t4

val tshift_eforall: k:knd -> e:exp -> x:nat -> Lemma (requires True)
                    (ensures (tshift_up_above_e x (EForT k e) =
                              EForT k (tshift_up_above_e (x + 1) e)))
let rec tshift_eforall k e x =
  assert(tshift_up_above_e x (EForT k e) = esubst_t (EForT k e) (tsub_inc_above x));
  esubst_tforall_hoist k e (tsub_inc_above x);
  assert(tshift_up_above_e x (EForT k e) =
         EForT k (esubst_t e (esubst_tforall (tsub_inc_above x))));
  esubst_textensional (esubst_tforall (tsub_inc_above x)) (tsub_inc_above (x+1)) e

(* AR: look for a better proof *)
val tshifts_ereordering: x:nat -> y:nat{y >= x} -> e:exp -> Lemma (requires True)
                         (ensures (tshe x (tshe y e) = tshe (y + 1) (tshe x e)))
                         (decreases e)
let rec tshifts_ereordering x y e =
  match e with
    | EVar _ -> ()
    | EApp e1 e2 -> tshifts_ereordering x y e1; tshifts_ereordering x y e2
    | ETApp e1 t
    | ELam t e1 -> tshifts_reordering x y t; tshifts_ereordering x y e1
    | EForT k e1 ->
      tshift_eforall k e1 y;
      tshift_eforall k (tshe (y + 1) e1) x;
      tshifts_ereordering (x + 1) (y + 1) e1;
      tshift_eforall k e1 x;
      tshift_eforall k (tshe (x + 1) e1) (y + 1)

val tshifts_reordering_general: x:nat -> y:nat{y >= x} ->
                                Lemma (forall (s:typ). tsh x (tsh y s) =
                                                       tsh (y + 1) (tsh x s))
let tshifts_reordering_general x y = forall_intro (tshifts_reordering x y)

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

  | SBetaT: k:knd ->
            e:exp ->
            t:typ ->
            step (ETApp (EForT k e) t) (esubst_tbeta t e)

  | STApp1: #e:exp -> #e':exp ->
            t:typ ->
            step e e' ->
            step (ETApp e t) (ETApp e' t)

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

  | KiFor : #g:env -> #t:typ ->
            k:knd ->
            kinding (extend_tvar g 0 k) t KTyp ->
            kinding g (TFor k t) KTyp

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

  | EqFor:  #t:typ -> #t':typ ->
            k:knd ->
            tequiv t t' ->
            tequiv (TFor k t) (TFor k t')

type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
            x:var{is_Some (lookup_evar g x)} ->
            kinding g (Some.v (lookup_evar g x)) KTyp ->
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

  | TyFor : #g:env -> #e:exp -> #t:typ ->
            k:knd ->
            typing (extend_tvar g 0 k) e t ->
            typing g (EForT k e) (TFor k t)

  | TyAppT: #g:env -> #e:exp -> #t:typ -> #t':typ ->
            k:knd ->
            typing g e (TFor k t') ->
            kinding g t k ->
            typing g (ETApp e t) (tsubst_beta t t')

val is_value : exp -> Tot bool
let is_value = fun e -> is_ELam e || is_EForT e

val tappears_free_in : x:var -> t:typ -> Tot bool (decreases t)
let rec tappears_free_in x t =
  match t with
  | TVar y -> x = y
  | TArr t1 t2
  | TApp t1 t2 -> tappears_free_in x t1 || tappears_free_in x t2
  | TFor _ t1
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
    | KiFor k1 h1 -> KiFor k1 (tcontext_invariance h1 (extend_tvar g' 0 k1))
    | KiLam k1 h1 -> KiLam k1 (tcontext_invariance h1 (extend_tvar g' 0 k1))
    | KiApp h1 h2 -> KiApp (tcontext_invariance h1 g') (tcontext_invariance h2 g')
    | KiArr h1 h2 -> KiArr (tcontext_invariance h1 g') (tcontext_invariance h2 g')

val eappears_free_in : x:var -> e:exp -> Tot bool (decreases e)
let rec eappears_free_in x e =
  match e with
    | EVar y -> x = y
    | EApp e1 e2 -> eappears_free_in x e1 || eappears_free_in x e2
    | ELam _ e1 -> eappears_free_in (x+1) e1
    | EForT _ e1 -> eappears_free_in x e1
    | ETApp e1 _ -> eappears_free_in x e1

val eappears_tfree_in : tx:var -> e:exp -> Tot bool (decreases e)
let rec eappears_tfree_in tx e =
  match e with
    | EVar _ -> false
    | EApp e1 e2 -> eappears_tfree_in tx e1 || eappears_tfree_in tx e2
    | ELam _ e1 -> eappears_tfree_in tx e1
    | EForT _ e1 -> eappears_tfree_in (tx + 1) e1
    | ETApp e1 t -> eappears_tfree_in tx e1 || tappears_free_in tx t


(* g1 and g2 are the same on the type variables,
   but they can vary on the unused term variables *)
opaque logic type EnvEqualE (e:exp) (g1:env) (g2:env) =
		 (forall (x:var). eappears_free_in x e ==>
                    lookup_evar g1 x = lookup_evar g2 x) /\
		 (FEq (MkEnv.a g1) (MkEnv.a g2))

(* g |- t :: k, g and g' are same for type variables, then g' |- t :: k *)
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
    | KiFor k h1 -> KiFor k (kinding_extensional h1 (extend_tvar g' 0 k))

opaque val econtext_invariance : #e:exp -> #g:env -> #t:typ ->
      h:(typing g e t) -> g':env{EnvEqualE e g g'} ->
      Tot (typing g' e t) (decreases h)
let rec econtext_invariance _ _ t h g' =
  match h with
    | TyVar x h -> TyVar x (kinding_extensional h g')
    | TyLam #g t_y #e1 #t' hk h1 ->
      TyLam t_y (tcontext_invariance hk g')
    	(econtext_invariance #e1 #(extend_evar g 0 t_y) #t' h1
    	   (extend_evar g' 0 t_y))
    | TyApp h1 h2 -> TyApp (econtext_invariance h1 g')
                           (econtext_invariance h2 g')
    | TyEqu h1 eq k -> TyEqu (econtext_invariance h1 g') eq (kinding_extensional k g')
    | TyFor k h1 -> TyFor k (econtext_invariance h1 (extend_tvar g' 0 k))
    | TyAppT #g #e #t #t' k h1 hk ->
      (* AR: doesn't work without implicits *)
      TyAppT #g' #e #t #t' k (econtext_invariance h1 g') (kinding_extensional  hk g')

(* kinding weakening when a term variable binding is added to env *)
opaque val kinding_weakening_ebnd : #g:env -> #t:typ -> #k:knd ->
      h:(kinding g t k) -> x:var -> t':typ ->
      Tot (kinding (extend_evar g x t') t k)
let kinding_weakening_ebnd g t k h x t' = kinding_extensional h (extend_evar g x t')

val esub_inc_above : nat -> var -> Tot exp
let esub_inc_above x y = if y<x then EVar y else EVar (y+1)

val eshift_up_above : nat -> exp -> Tot exp
let eshift_up_above x e = esubst e (esub_inc_above x)

val eshift_up : exp -> Tot exp
let eshift_up = eshift_up_above 0

val eshift_up_above_lam: n:nat -> t:typ -> e:exp -> Lemma
  (ensures (eshift_up_above n (ELam t e) = ELam t (eshift_up_above (n + 1) e)))
let eshift_up_above_lam n t e =
  assert(eshift_up_above n (ELam t e) = esubst (ELam t e) (esub_inc_above n));
  esubst_lam_hoist t e (esub_inc_above n);
  assert(eshift_up_above n (ELam t e) =
         ELam t (esubst e (esubst_lam (esub_inc_above n))));
  esubst_extensional (esubst_lam (esub_inc_above n)) (esub_inc_above (n+1)) e

val eshift_up_above_for: n:nat -> k:knd -> e:exp -> Lemma (requires True)
                         (ensures (eshift_up_above n (EForT k e) = EForT k (eshift_up_above n e)))
let eshift_up_above_for n k e =
  esubst_forallt_hoist k e (esub_inc_above n);
  esubst_extensional (esubst_forallt (esub_inc_above n)) (esub_inc_above n) e;
  ()

val esubst_tbeta_gen_for: x:nat -> t:typ -> k:knd -> e:exp -> Lemma (requires True)
                          (ensures (esubst_tbeta_gen x t (EForT k e) = EForT k (esubst_tbeta_gen (x + 1) (tshift_up_above 0 t) e)))
let esubst_tbeta_gen_for x t k e =
  assert(esubst_tbeta_gen x t (EForT k e) =
           esubst_t (EForT k e) (tsub_beta_gen x t));
  esubst_tforall_hoist k e (tsub_beta_gen x t);
  assert(esubst_tbeta_gen x t (EForT k e) =
           EForT k (esubst_t e (esubst_tforall (tsub_beta_gen x t))));

  assert(EForT k (esubst_tbeta_gen (x + 1) (tshift_up t) e) =
           EForT k (esubst_t e (tsub_beta_gen (x + 1) (tshift_up t))));

  forall_intro (* #var #(tsubst_gen_tlam_aux_type t x) *) (tsubst_gen_tlam_aux t x);

  esubst_textensional (esubst_tforall (tsub_beta_gen x t))
                      (tsub_beta_gen (x + 1) (tshift_up t)) e

(* kinding weakening when a type variable binding is added to env *)
opaque val kinding_weakening_tbnd : #g:env -> #t:typ -> #k:knd ->
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
    | KiFor #g #t k h1 ->
      tshift_up_above_lam x k t;
      let h2 = kinding_weakening_tbnd h1 (x + 1) KTyp in
      KiFor k (kinding_extensional h2 (extend_tvar (extend_tvar g x k') 0 k))

(* kinding strengthening from TAPL (Lemma 30.3.1),
   just an instance of kinding_extensional; used often *)
opaque val kinding_strengthening_ebnd : g:env -> x:var -> t_x:typ -> #t:typ -> #k:knd ->
      h:(kinding (extend_evar g x t_x) t k) ->
      Tot (kinding g t k) (decreases h)
let kinding_strengthening_ebnd g x t_x t k h = kinding_extensional h g

opaque val kinding_inversion_arrow: #g:env -> #t1:typ -> #t2:typ ->
                             h:(kinding g (TArr t1 t2) KTyp) ->
                             Tot (cand (kinding g t1 KTyp) (kinding g t2 KTyp))
let rec kinding_inversion_arrow g t1 t2 h = match h with
  | KiArr h1 h2 -> Conj h1 h2

opaque val kinding_inversion_forall: #g:env -> #k:knd -> #t:typ ->
                             h:(kinding g (TFor k t) KTyp) ->
                             Tot (kinding (extend_tvar g 0 k) t KTyp)
let rec kinding_inversion_forall g t1 t2 h = match h with
  | KiFor k1 h1 -> h1

val eshift_free_lemma: e:exp -> x:nat{eappears_free_in x e = false} -> Lemma (requires True)
                       (ensures (eappears_free_in x (eshift_up_above x e) = false))
let rec eshift_free_lemma e x =
  match e with
    | EVar y -> ()
    | EApp e1 e2 -> eshift_free_lemma e1 x; eshift_free_lemma e2 x
    | ELam t e1 ->
      eshift_up_above_lam x t e1;
      eshift_free_lemma e1 (x + 1)
    | EForT k e1 ->
      eshift_up_above_for x k e1;
      eshift_free_lemma e1 x
    | ETApp e1 t -> eshift_free_lemma e1 x

(* this folows from functional extensionality *)
opaque val typing_extensional: #g:env -> #e:exp -> #t:typ -> h:(typing g e t) ->
                g':env{FEq (MkEnv.x g) (MkEnv.x g') /\
                       FEq (MkEnv.a g) (MkEnv.a g')} ->
                Tot (typing g' e t) (decreases h)
let rec typing_extensional _ _ _ h g' = h

(* typing weakening when term variable is added to env *)
opaque val typing_weakening_ebnd: #g:env -> x:var -> t_x:typ -> #e:exp{eappears_free_in x e = false} -> #t:typ ->
      h:(typing g e t) -> Tot (typing (extend_evar g x t_x)
                                      (eshift_up_above x e) t) (decreases h)
let rec typing_weakening_ebnd g x t_x e t h =
  match h with
    | TyVar y h ->
      let h1 = kinding_weakening_ebnd h x t_x in
      if y < x then TyVar y h1 else TyVar (y+1) h1
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
    | TyFor #g #e1 #t1 k h1 ->
      let h11 = typing_weakening_ebnd x t_x h1 in
      eshift_up_above_for x k e1;
      eshift_free_lemma e1 x;
      TyFor k (econtext_invariance h11 (extend_tvar (extend_evar g x t_x) 0 k))
    | TyAppT #dc #e1 #t1 #t2 k h1 hk ->
      let h11 = typing_weakening_ebnd #g x t_x #e1 #(TFor k t2) h1 in
      let hk1 = kinding_weakening_ebnd #g #t1 #k hk x t_x in
      TyAppT #(extend_evar g x t_x) #(eshift_up_above x e1) #t1 #t2 k h11 hk1

opaque type tshift_up_above_tsubst_beta_aux_typ (x:var) (t2:typ) (y:var) =
  (tsub_comp (tsub_inc_above x) (tsub_beta_gen 0 t2) y =
   tsub_comp (tsub_beta_gen 0 (tsubst t2 (tsub_inc_above x)))
             (tsub_inc_above (x+1)) y)

val tshift_up_above_tsubst_beta_aux : x:var -> t2:typ -> y:var ->
      Lemma (tshift_up_above_tsubst_beta_aux_typ x t2 y)
let tshift_up_above_tsubst_beta_aux x t2 y = ()

val tshift_up_above_tsubst_beta : x:var -> t1:typ -> t2:typ -> Lemma
    (ensures (tshift_up_above x (tsubst_beta t2 t1) =
              tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1)))
    (decreases t1)
let rec tshift_up_above_tsubst_beta x t1 t2 =
  assert(tshift_up_above x (tsubst_beta t2 t1) =
         tsubst (tsubst_beta t2 t1) (tsub_inc_above x));
  assert(tshift_up_above x (tsubst_beta t2 t1) =
         tsubst (tsubst t1 (tsub_beta_gen 0 t2)) (tsub_inc_above x));
  tsubst_comp (tsub_inc_above x) (tsub_beta_gen 0 t2) t1;
  assert(tshift_up_above x (tsubst_beta t2 t1) =
         tsubst t1 (tsub_comp (tsub_inc_above x) (tsub_beta_gen 0 t2)));

  assert(tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1) =
         tsubst (tshift_up_above (x + 1) t1)
                (tsub_beta_gen 0 (tshift_up_above x t2)));
  assert(tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1) =
         tsubst (tsubst t1 (tsub_inc_above (x+1)))
                (tsub_beta_gen 0 (tsubst t2 (tsub_inc_above x))));
  tsubst_comp (tsub_beta_gen 0 (tsubst t2 (tsub_inc_above x)))
              (tsub_inc_above (x+1)) t1;
  assert(tsubst_beta (tshift_up_above x t2) (tshift_up_above (x + 1) t1) =
         tsubst t1 (tsub_comp (tsub_beta_gen 0 (tsubst t2 (tsub_inc_above x)))
                              (tsub_inc_above (x+1))));
  forall_intro (* #var #(tshift_up_above_tsubst_beta_aux_typ x t2) *)
               (tshift_up_above_tsubst_beta_aux x t2); (* only for speedup *)
  tsubst_extensional (tsub_comp (tsub_inc_above x) (tsub_beta_gen 0 t2))
                     (tsub_comp (tsub_beta_gen 0 (tsubst t2 (tsub_inc_above x)))
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
    | EqFor #t #t' k h1 ->
      tshift_up_above_lam x k t;
      tshift_up_above_lam x k t';
      EqFor k (tequiv_tshift h1 (x + 1))


opaque type esubst_gen_elam_aux_type (e:exp) (x:var) (y:var) =
  (esubst_lam (esub_beta_gen x e) y = esub_beta_gen (x + 1) (eshift_up e) y)
val esubst_gen_elam_aux : e:exp -> x:var -> y:var ->
                          Lemma (esubst_gen_elam_aux_type e x y)
let esubst_gen_elam_aux e x y =
  match y with
    | 0 -> ()
    | _ ->
      (assert(esubst_lam (esub_beta_gen x e) y =
          esubst (esub_beta_gen x e (y-1)) esub_inc);
       assert(esub_beta_gen (x + 1) (eshift_up e) y =
           esub_beta_gen (x + 1) (esubst e (esub_inc_above 0)) y);
       if (y-1) < x then ()
       else if y-1 = x then
         (assert(esubst_lam (esub_beta_gen x e) y =
             esubst e esub_inc);
          assert(esub_beta_gen (x + 1) (eshift_up e) y =
              esubst e (esub_inc_above 0));
          esubst_extensional esub_inc (esub_inc_above 0) e)
       else ())

val esubst_gen_elam : x:var -> e:exp -> t:typ -> e':exp -> Lemma
                      (ensures (esubst_beta_gen x e (ELam t e') =
                       ELam t (esubst_beta_gen (x + 1) (eshift_up e) e')))
let esubst_gen_elam x e t e' =
  assert(esubst_beta_gen x e (ELam t e') =
           esubst (ELam t e') (esub_beta_gen x e));
  esubst_lam_hoist t e' (esub_beta_gen x e);
  assert(esubst_beta_gen x e (ELam t e') =
           ELam t (esubst e' (esubst_lam (esub_beta_gen x e))));

  assert(ELam t (esubst_beta_gen (x + 1) (eshift_up e) e') =
           ELam t (esubst e' (esub_beta_gen (x + 1) (eshift_up e))));

  forall_intro (* #var #(esubst_gen_elam_aux_type e x) *) (esubst_gen_elam_aux e x);

  esubst_extensional (esubst_lam (esub_beta_gen x e))
                     (esub_beta_gen (x + 1) (eshift_up e)) e'


val esubst_gen_efor: x:var -> v:exp -> k:knd -> e:exp -> Lemma (requires True)
                     (ensures (esubst_beta_gen x v (EForT k e) =
                               EForT k (esubst_beta_gen x (esubst_t v tsub_inc) e)))
let esubst_gen_efor x v k e =
  esubst_forallt_hoist k e (esub_beta_gen x v);
  esubst_extensional (esubst_forallt (esub_beta_gen x v)) (esub_beta_gen x (esubst_t v tsub_inc)) e

type rl =
  | RNil:  rl
  | RSnoc: tl:rl -> hd:typ -> rl

val rlen: l:rl -> Tot nat
let rec rlen l = match l with
  | RNil -> 0
  | RSnoc tl _ -> rlen tl + 1

val lookup_rl: l:rl -> x:var -> Tot (r:option typ{x < rlen l  ==> is_Some r /\
                                                  x >= rlen l ==> is_None r})
let rec lookup_rl l x = match l with
  | RNil -> None
  | RSnoc tl hd -> if x = 0 then Some hd else lookup_rl tl (x - 1)

(* AR: why do I need this ! *)
val redundant_lemma: l:rl -> x:nat -> Lemma (requires True)
                                      (ensures (x < rlen l ==> is_Some (lookup_rl l x))) (decreases l)
let rec redundant_lemma l x = match l with
  | RNil -> ()
  | RSnoc tl hd -> if x = 0 then () else redundant_lemma tl (x - 1)

val extend_rl: g:env -> l:rl -> Tot env
let extend_rl g l =
  let a_env = fun a -> lookup_tvar g a in
  let x_env = fun x -> if x < rlen l then lookup_rl l x else
                       lookup_evar g (x - rlen l)
  in
  MkEnv a_env x_env

val extend_rl_tlookup_lemma: g:env -> l:rl -> Lemma (requires True)
                             (ensures (FEq (MkEnv.a (extend_rl g l)) (MkEnv.a g)))
let extend_rl_tlookup_lemma g l = ()


val extend_rl_elookup_lemma: g:env -> l:rl -> x:nat -> Lemma (requires True)
                             (ensures ((x < rlen l ==> lookup_evar (extend_rl g l) x = lookup_rl l x) /\
                                       (x >= rlen l ==> lookup_evar (extend_rl g l) x = lookup_evar g (x - rlen l))))
let extend_rl_elookup_lemma g l x = ()

val rmap: l:rl -> f:(typ -> Tot typ) -> Tot (l':rl{rlen l' = rlen l})
let rec rmap l f = match l with
  | RNil -> RNil
  | RSnoc tl hd -> RSnoc (rmap tl f) (f hd)

val rmap_lookup_lemma: l:rl -> f:(typ -> Tot typ) -> x:nat{is_Some (lookup_rl l x)} ->
                       Lemma (requires True)
                       (ensures (is_Some (lookup_rl (rmap l f) x) /\
                                 Some.v (lookup_rl (rmap l f) x) =
                                 f (Some.v (lookup_rl l x))))
let rec rmap_lookup_lemma l f x = match l with
  | RSnoc tl hd -> if x = 0 then () else rmap_lookup_lemma tl f (x - 1)

(* AR: these were amazingly auto :) *)
val combine_with_rl_lemma1: g:env -> l:rl -> t:typ -> x:nat -> Lemma (requires True)
                            (ensures (lookup_evar (extend_evar (extend_rl g l) 0 t) x =
                                      lookup_evar (extend_rl g (RSnoc l t)) x))
let combine_with_rl_lemma1 g l t x = () (* AR: these go through *)

val combine_with_rl_lemma2: g:env -> l:rl -> t:typ -> x:nat -> Lemma (requires True)
                           (ensures (lookup_tvar (extend_evar (extend_rl g l) 0 t) x =
                                     lookup_tvar (extend_rl g (RSnoc l t)) x))
let combine_with_rl_lemma2 g l t x = () (* AR: this too *)

(* AR: how can I prove this given above two lemmas *)
val combine_with_rl_ext: g:env -> l:rl -> t:typ -> Lemma (requires True)
                         (ensures (FEq (MkEnv.a (extend_evar (extend_rl g l) 0 t))
                                       (MkEnv.a (extend_rl g (RSnoc l t))) /\
				   FEq (MkEnv.x (extend_evar (extend_rl g l) 0 t))
                                       (MkEnv.x (extend_rl g (RSnoc l t)))))
let combine_with_rl_ext g l t = admit ()

val commute_with_rl_lemma1: g:env -> x:nat -> k_x:knd -> l:rl -> k:knd -> y:nat ->
  Lemma (requires True)
        (ensures lookup_tvar (extend_tvar (extend_rl (extend_tvar g x k_x) l) 0 k) y =
                 lookup_tvar (extend_rl (extend_tvar (extend_tvar g 0 k) (x + 1) k_x) (rmap l (tshift_up_above 0))) y)
let commute_with_rl_lemma1 g x k_x l k y = () (* AR this goes through but long time *)

val commute_with_rl_lemma2: g:env -> x:nat -> k_x:knd -> l:rl -> k:knd -> y:var ->
  Lemma (requires True)
        (ensures lookup_evar (extend_tvar (extend_rl (extend_tvar g x k_x) l) 0 k) y =
                 lookup_evar (extend_rl (extend_tvar (extend_tvar g 0 k) (x + 1) k_x) (rmap l (tshift_up_above 0))) y)
let commute_with_rl_lemma2 g x k_x l k y = (* AR: goes through, long time *)
  if y < rlen l then
    let _ = redundant_lemma l y in
    rmap_lookup_lemma l (tshift_up_above 0) y
  else
    let _ = extend_rl_elookup_lemma g l y in
    if is_Some (lookup_evar g (y - rlen l)) then
      let t' = Some.v (lookup_evar g (y - rlen l)) in
      tshifts_reordering 0 x t';
      tshifts_ereordering 0 x (EVar y)
    else
      ()

(* AR: same as above, how do I prove this given above 2 *)
val commute_with_rl_ext: g:env -> x:nat -> k_x:knd -> l:rl -> k:knd ->
  Lemma (requires True)
        (ensures (FEq (MkEnv.a (extend_tvar (extend_rl (extend_tvar g x k_x) l) 0 k))
                      (MkEnv.a (extend_rl (extend_tvar (extend_tvar g 0 k) (x + 1) k_x) (rmap l (tshift_up_above 0)))) /\
                  FEq (MkEnv.x (extend_tvar (extend_rl (extend_tvar g x k_x) l) 0 k))
                      (MkEnv.x (extend_rl (extend_tvar (extend_tvar g 0 k) (x + 1) k_x) (rmap l (tshift_up_above 0))))))
let commute_with_rl_ext g x k_x l k = admit ()


val commute_with_rl2_lemma1: g:env -> l:rl -> k:knd -> y:nat ->
  Lemma (requires True)
        (ensures lookup_tvar (extend_tvar (extend_rl g l) 0 k) y =
                 lookup_tvar (extend_rl (extend_tvar g 0 k) (rmap l (tshift_up_above 0))) y)
let commute_with_rl2_lemma1 g l k y = () (* AR: goes through *)

val commute_with_rl2_lemma2: g:env -> l:rl -> k:knd -> y:nat ->
  Lemma (requires True)
        (ensures lookup_evar (extend_tvar (extend_rl g l) 0 k) y =
                 lookup_evar (extend_rl (extend_tvar g 0 k) (rmap l (tshift_up_above 0))) y)
let commute_with_rl2_lemma2 g l k y = (* AR: goes through *)
  if y < rlen l then
    let _ = redundant_lemma l y in
    rmap_lookup_lemma l (tshift_up_above 0) y
  else
    let _ = extend_rl_elookup_lemma g l y in
    ()

(* AR: third case, how to prove *)
val commute_with_rl2_ext: g:env -> l:rl -> k:knd ->
  Lemma (requires True)
        (ensures (FEq (MkEnv.a (extend_tvar (extend_rl g l) 0 k))
                      (MkEnv.a (extend_rl (extend_tvar g 0 k) (rmap l (tshift_up_above 0)))) /\
		  FEq (MkEnv.x (extend_tvar (extend_rl g l) 0 k))
                      (MkEnv.x (extend_rl (extend_tvar g 0 k) (rmap l (tshift_up_above 0))))))
let commute_with_rl2_ext g l k = admit ()


val tsubst_commute_helper_rl: x:nat -> y:nat{x >= y} -> s:typ -> l:rl -> Lemma (requires True)
                              (ensures (rmap (rmap l (ts x s)) (tsh y) =
                                        rmap (rmap l (tsh y)) (ts (x + 1) (tsh y s))))
                              (decreases l)
let rec tsubst_commute_helper_rl x y s l =
  match l with
    | RNil -> ()
    | RSnoc tl hd ->
      tsubst_commute_helper x y s hd;
      tsubst_commute_helper_rl x y s tl


val shift_up_above_rl: l:rl -> x:nat -> Tot rl
let shift_up_above_rl l x = rmap l (tshift_up_above x)

val subst_beta_gen_rl: l:rl -> y:nat -> t:typ -> Tot rl
let subst_beta_gen_rl l y t = rmap l (tsubst_beta_gen y t)


(* typing weakening when type variable binding is added to env *)
(* NS: This one alone takes ~4-5 secs to prove *)
opaque val typing_weakening_tbnd: #g:env -> x:var -> k_x:knd -> #e:exp -> #t:typ ->
      h:(typing g e t) ->
      Tot (typing (extend_tvar g x k_x)
                  (tshift_up_above_e x e) (tshift_up_above x t)) (decreases h)
let rec typing_weakening_tbnd g x k_x e t h = magic()
(* CH: this fails for me even with timeout 60
  match h with
    | TyVar y h -> TyVar y (kinding_weakening_tbnd h x k_x)
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
    | TyFor #g #e1 #t1 k h1 ->
      let h2 = typing_weakening_tbnd #(extend_tvar g 0 k) (x + 1) k_x #e1 #t1 h1 in
      commute_with_rl_ext g x k_x RNil k;
      let h3 = typing_extensional #(extend_tvar (extend_tvar g 0 k) (x + 1) k_x) #(tshift_up_above_e (x + 1) e1) #(tshift_up_above (x + 1) t1) h2 (extend_tvar (extend_tvar g x k_x) 0 k) in
      tshift_eforall k e1 x;
      tshift_up_above_lam x k t1;
      TyFor #(extend_tvar g x k_x) #(tshift_up_above_e (x + 1) e1) #(tshift_up_above (x + 1) t1) k h3
    | TyAppT #dc #e1 #t1 #t2 k h1 h2 ->
      let h11 = typing_weakening_tbnd #g x k_x #e1 #(TFor k t2) h1 in
      tshift_up_above_lam x k t2;
      let h2' = kinding_weakening_tbnd #g #t1 #k h2 x k_x in
      tsubst_commute2 0 x t1 t2;
      TyAppT #(extend_tvar g x k_x) #(tshift_up_above_e x e1) #(tshift_up_above x t1) #(tshift_up_above (x + 1) t2) k h11 h2'
*)

opaque val typing_substitution: x:nat -> #e:exp -> #v:exp -> #t_x:typ -> #t:typ ->
      #g:env -> h1:(typing g v t_x) -> h2:(typing (extend_evar g x t_x) e t) ->
      Tot (typing g (esubst_beta_gen x v e) t) (decreases %[e;h2])
let rec typing_substitution x e v t_x t g h1 h2 =
  match h2 with
    | TyVar y hk ->
      if x = y then h1
      else if y < x then econtext_invariance h2 g
      else TyVar (y - 1) (kinding_strengthening_ebnd g x t_x hk)
    | TyLam #g' t_y #e' #t' kh h21 ->
      let h21' = typing_extensional h21
                   (extend_evar (extend_evar g 0 t_y) (x+1) t_x) in
      let h1' = typing_weakening_ebnd 0 t_y h1 in
      esubst_gen_elam x v t_y e';
      TyLam t_y (kinding_extensional kh g) (typing_substitution (x + 1) h1' h21')
    | TyApp h21 h22 ->
      TyApp (typing_substitution x h1 h21) (typing_substitution x h1 h22)
    | TyEqu h21 eq kh ->
      TyEqu (typing_substitution x h1 h21) eq
        (kinding_strengthening_ebnd g x t_x kh)
    | TyFor #g'' #e1 #t1 k h3 ->
      let h31 = typing_extensional h3 (extend_evar (extend_tvar g 0 k) x (tshift_up t_x)) in
      let h11 = typing_weakening_tbnd 0 k h1 in
      let h32 = typing_substitution x h11 h31 in
      esubst_gen_efor x v k e1;
      esubst_textensional tsub_inc (tsub_inc_above 0) v;
      (* AR: does not work without implicits, try out equality constraint *)
      TyFor #g #(esubst_beta_gen x (tshift_up_above_e 0 v) e1) #t1 k h32
    | TyAppT #g' #e1 #t1 #t2 k h3 hk ->
      let h22 = typing_substitution x h1 h3 in
      let hk1 = kinding_strengthening_ebnd g x t_x hk in
      (* AR: again implicits required *)
      TyAppT #g #(esubst_beta_gen x v e1) #t1 #t2 k h22 hk1

(* The (pleasant) surprise here is that (as opposed to TAPS) we didn't
   have to also apply the substitution within the MkEnv.x part of the
   environment. That's because kinding completely ignores that part.
   So we don't even ensure that it's well formed in any way after
   substitution. Unfortunately this joy won't last long. *)
opaque val kinding_substitution: x:nat -> #t1:typ -> #t:typ -> #k_x:knd -> #k1:knd ->
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
    | KiFor #g' #t2 k2 h21 ->
      let h21' = kinding_extensional h21 (extend_tvar (extend_tvar g 0 k2) (x + 1) k_x) in
      let h11 = kinding_weakening_tbnd h1 0 k2 in
      let h22 = kinding_substitution (x + 1) h11 h21' in
      tsubst_gen_tlam x t k2 t2;
      KiFor k2 h22

opaque val kinding_substitution_l: x:nat -> #t1:typ -> #t:typ -> #k_x:knd -> #k1:knd -> #l:rl ->
      #g:env -> h1:(kinding g t k_x) ->
      h2:(kinding (extend_rl (extend_tvar g x k_x) l) t1 k1) ->
      Tot (kinding (extend_rl g (subst_beta_gen_rl l x t)) (tsubst_beta_gen x t t1) k1) (decreases t1)
let rec kinding_substitution_l x t1 t k_x k1 l g h1 h2 =
  let ha = tcontext_invariance #t1 #(extend_rl (extend_tvar g x k_x) l) #k1 h2 (extend_tvar g x k_x) in
  let hb = kinding_substitution x #t1 #t #k_x #k1 #g h1 ha in
  tcontext_invariance #(tsubst_beta_gen x t t1) #g #k1 hb (extend_rl g (subst_beta_gen_rl l x t))

opaque val tequiv_tsubst: t1:typ -> t2:typ -> x:nat -> t:typ ->
                   h:tequiv t1 t2 ->
                   Tot (tequiv (tsubst_beta_gen x t t1) (tsubst_beta_gen x t t2))
		   (decreases h)
let rec tequiv_tsubst t1 t2 x t h =
  match h with
    | EqLam #t3 #t4 k h' ->
      let h1 = tequiv_tsubst t3 t4 (x + 1) (tshift_up_above 0 t) h' in
      tsubst_gen_tlam x t k t3;
      tsubst_gen_tlam x t k t4;
      EqLam #(tsubst_beta_gen (x + 1) (tshift_up_above 0 t) t3) #(tsubst_beta_gen (x + 1) (tshift_up_above 0 t) t4) k h1
    | EqBeta k t3 t4 ->
      tsubst_gen_tlam x t k t3;
      tsubst_commute t3 0 t4 x t;
      EqBeta k (tsubst_beta_gen (x + 1) (tshift_up_above 0 t) t3) (tsubst_beta_gen x t t4)
    | EqFor #t3 #t4 k h' ->
      let h1 = tequiv_tsubst t3 t4 (x + 1) (tshift_up_above 0 t) h' in
      tsubst_gen_tlam x t k t3;
      tsubst_gen_tlam x t k t4;
      EqFor #(tsubst_beta_gen (x + 1) (tshift_up_above 0 t) t3) #(tsubst_beta_gen (x + 1) (tshift_up_above 0 t) t4) k h1
    | EqRefl _ -> EqRefl (tsubst_beta_gen x t t1)
    | EqSymm #t2 #t1 h' ->
      EqSymm (tequiv_tsubst t2 t1 x t h')
    | EqApp #t3 #t3' #t4 #t4' h1 h2 ->
      EqApp (tequiv_tsubst t3 t3' x t h1) (tequiv_tsubst t4 t4' x t h2)
    | EqArr #t3 #t3' #t4 #t4' h1 h2 ->
      EqArr (tequiv_tsubst t3 t3' x t h1) (tequiv_tsubst t4 t4' x t h2)
    | EqTran #t3 #t4 #t5 h1 h2 ->
      EqTran (tequiv_tsubst t3 t4 x t h1) (tequiv_tsubst t4 t5 x t h2)

opaque val typing_substitution_t_l: x:nat -> #e:exp -> #t1:typ -> #k_x:knd -> #t2:typ -> #g:env -> #l:rl ->
                           h1:kinding g t1 k_x ->
                           h2:typing (extend_rl (extend_tvar g x k_x) l) e t2 ->
                           Tot (typing (extend_rl g (subst_beta_gen_rl l x t1))
                                       (esubst_tbeta_gen x t1 e)
                                       (tsubst_beta_gen x t1 t2)) (decreases %[e;h2])
let rec typing_substitution_t_l x e t1 k_x t2 g l h1 h2 =
  match h2 with
    | TyVar y hk ->
      if y < rlen l then
      	let _ = rmap_lookup_lemma l (tsubst_beta_gen x t1) y in
      	TyVar #(extend_rl g (subst_beta_gen_rl l x t1)) y (kinding_substitution_l x #t2 #t1 #k_x #KTyp #l #g h1 hk)
      else
      	let y' = y - rlen l in
      	let t' = Some.v (lookup_evar g y') in
      	shift_above_and_subst t' x t1;
      	TyVar #(extend_rl g (subst_beta_gen_rl l x t1)) y (kinding_substitution_l x #t2 #t1 #k_x #KTyp #l #g h1 hk)

    | TyLam #dc #t3 #e3 #t4 h2k h21 ->
      combine_with_rl_ext (extend_tvar g x k_x) l t3;
      let h21' = typing_extensional #(extend_evar (extend_rl (extend_tvar g x k_x) l) 0 t3) #e3 #t4 h21 (extend_rl (extend_tvar g x k_x) (RSnoc l t3)) in
      let h22 = typing_substitution_t_l x #e3 #t1 #k_x #t4 #g #(RSnoc l t3) h1 h21' in

      combine_with_rl_ext g (rmap l (tsubst_beta_gen x t1)) (tsubst_beta_gen x t1 t3);
      let h22' = typing_extensional #(extend_rl g (rmap (RSnoc l t3) (tsubst_beta_gen x t1))) #(esubst_tbeta_gen x t1 e3) #(tsubst_beta_gen x t1 t4) h22 (extend_evar (extend_rl g (rmap l (tsubst_beta_gen x t1))) 0 (tsubst_beta_gen x t1 t3)) in

      let h2k' = kinding_substitution_l x #t3 #t1 #k_x #KTyp #l #g h1 h2k in

      TyLam #(extend_rl g (rmap l (tsubst_beta_gen x t1))) #(tsubst_beta_gen x t1 t3) #(esubst_tbeta_gen x t1 e3) #(tsubst_beta_gen x t1 t4) h2k' h22'

    | TyApp #dc #e1 #e2 #t3 #t4 h21 h22 ->
      let h21' = typing_substitution_t_l x #e1 #t1 #k_x #(TArr t3 t4) #g #l h1 h21 in
      let h22' = typing_substitution_t_l x #e2 #t1 #k_x #t3 #g #l h1 h22 in
      TyApp #(extend_rl g (rmap l (tsubst_beta_gen x t1))) #(esubst_tbeta_gen x t1 e1) #(esubst_tbeta_gen x t1 e2) #(tsubst_beta_gen x t1 t3) #(tsubst_beta_gen x t1 t4) h21' h22'

    | TyEqu #dc1 #dc2 #t3 #dc h21 h22 h23 ->
      let h21' = typing_substitution_t_l x #e #t1 #k_x #t3 #g #l h1 h21 in
      let h22' = tequiv_tsubst t3 t2 x t1 h22 in
      let h23' = kinding_substitution_l x #t2 #t1 #k_x #KTyp #l #g h1 h23 in

      TyEqu #(extend_rl g (rmap l (tsubst_beta_gen x t1))) #(esubst_tbeta_gen x t1 e) #(tsubst_beta_gen x t1 t3) #(tsubst_beta_gen x t1 t2) h21' h22' h23'

    | TyFor #dc #e3 #t3 k h21 ->
      commute_with_rl_ext g x k_x l k;
      let h21' = typing_extensional #(extend_tvar (extend_rl (extend_tvar g x k_x) l) 0 k) #e3 #t3 h21 (extend_rl (extend_tvar (extend_tvar g 0 k) (x + 1) k_x) (rmap l (tshift_up_above 0))) in
      let h1' = kinding_weakening_tbnd #g #t1 #k_x h1 0 k in
      let h22 = typing_substitution_t_l (x + 1) #e3 #(tshift_up_above 0 t1) #k_x #t3 #(extend_tvar g 0 k) #(rmap l (tshift_up_above 0)) h1' h21' in
      tsubst_commute_helper_rl (x + 1) 0 t1 l;
      commute_with_rl2_ext g (rmap l (tsubst_beta_gen x t1)) k;
      esubst_tbeta_gen_for x t1 k e3;
      tsubst_gen_tlam x t1 k t3;
      TyFor #(extend_rl g (rmap l (tsubst_beta_gen x t1))) #(esubst_tbeta_gen (x + 1) (tshift_up_above 0 t1) e3) #(tsubst_beta_gen (x + 1) (tshift_up_above 0 t1) t3) k h22

    | TyAppT #dc #e3 #t3 #t4 k h21 h22 ->
      let h21' = typing_substitution_t_l x #e3 #t1 #k_x #(TFor k t4) #g #l h1 h21 in
      tsubst_gen_tlam x t1 k t4;
      let h22' = kinding_substitution_l x #t1 #t3 #k_x #k #l #g h1 h22 in
      tsubst_commute t4 0 t3 x t1;
      TyAppT #(extend_rl g (rmap l (tsubst_beta_gen x t1))) #(esubst_tbeta_gen x t1 e3) #(tsubst_beta_gen x t1 t3) #(TFor k (tsubst_beta_gen (x + 1) (tshift_up_above 0 t1) t4)) k h21' h22'


opaque val typing_substitution_t: x:nat -> #e:exp -> #t1:typ -> #k_x:knd -> #t2:typ -> #g:env ->
                           h1:kinding g t1 k_x ->
                           h2:typing (extend_tvar g x k_x) e t2 ->
                           Tot (typing g
                                       (esubst_tbeta_gen x t1 e)
                                       (tsubst_beta_gen x t1 t2))
let typing_substitution_t x e t1 k_x t2 g h1 h2 =
  let h2a = typing_extensional #(extend_tvar g x k_x) #e #t2 h2 (extend_rl (extend_tvar g x k_x) RNil) in
  let h2b = typing_substitution_t_l x #e #t1 #k_x #t2 #g #RNil h1 h2a in
  typing_extensional #(extend_rl g (subst_beta_gen_rl RNil x t1)) #(esubst_tbeta_gen x t1 e) #(tsubst_beta_gen x t1 t2) h2b g

opaque val typing_to_kinding : #g:env -> #e:exp -> #t:typ ->
                                    h:(typing g e t) ->
                                    Tot (kinding g t KTyp) (decreases h)
let rec typing_to_kinding g e t h =
  match h with
    | TyVar x h -> h
    | TyLam t' hk h1 -> KiArr hk (kinding_strengthening_ebnd g 0 t'
                                    (typing_to_kinding h1))
    | TyApp #g #e1 #e2 #t1 #t2 h1 h2 ->
      let Conj pa pb = kinding_inversion_arrow #g #t1 #t2
        (typing_to_kinding h1) in pb
    | TyEqu h1 eq hk -> hk
    | TyFor k h1 -> KiFor k (typing_to_kinding h1)
    | TyAppT #dc #e1 #t1 #t2 k h1 h2 ->
      let h11 = typing_to_kinding #g #e1 #(TFor k t2) h1 in
      let h12 = kinding_inversion_forall #g #k #t2 h11 in
      kinding_substitution 0 #t2 #t1 #k #KTyp #g h2 h12

(* Parallel type reduction *)

type tred: typ -> typ -> Type =
  | TrRefl: t:typ ->
           tred t t

  | TrArr:  #t1:typ -> #t2:typ -> #t1':typ -> #t2':typ ->
           tred t1 t1' ->
           tred t2 t2' ->
           tred (TArr t1 t2) (TArr t1' t2')

  | TrLam:  #t1:typ -> #t2:typ ->
           k:knd ->
           h:tred t1 t2 ->
           tred (TLam k t1) (TLam k t2)

  | TrApp:  #t1:typ -> #t2:typ -> #t1':typ -> #t2':typ ->
           tred t1 t1' ->
           tred t2 t2' ->
           tred (TApp t1 t2) (TApp t1' t2')

  | TrBeta: #t1:typ -> #t2:typ -> #t1':typ -> #t2':typ ->
           k:knd ->
           tred t1 t1' ->
           tred t2 t2' ->
           tred (TApp (TLam k t1) t2) (tsubst_beta t2' t1')
  | TrFor: #t:typ -> #t':typ ->
           k:knd ->
           tred t t' ->
           tred (TFor k t) (TFor k t')

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
    | TrFor #t1 #t2 k h1  ->
      tshift_up_above_lam x k t1;
      tshift_up_above_lam x k t2;
      TrFor k (tred_shiftup_above (x + 1) h1)

(* Lemma 30.3.6: s => s' implies t[y |-> s] => t[y |-> s'] *)
opaque val subst_of_tred: #s:typ -> #s':typ -> x:nat -> t:typ ->
                   h:(tred s s') ->
                   Tot (tred (tsubst_beta_gen x s t) (tsubst_beta_gen x s' t))
		   (decreases t)
let rec subst_of_tred s s' x t h =
  match t with
    | TVar y ->
      if y < x then
    	TrRefl t
      else if y = x then
    	h
      else
    	TrRefl (TVar (y - 1))
    | TLam k t1 ->
      tsubst_gen_tlam x s k t1;
      tsubst_gen_tlam x s' k t1;
      TrLam k (subst_of_tred (x + 1) t1 (tred_shiftup_above 0 h))
    | TApp t1 t2 ->
      TrApp (subst_of_tred x t1 h) (subst_of_tred x t2 h)
    | TArr t1 t2 ->
      TrArr (subst_of_tred x t1 h) (subst_of_tred x t2 h)
    | TFor k t1 ->
      tsubst_gen_tlam x s k t1;
      tsubst_gen_tlam x s' k t1;
      TrFor k (subst_of_tred (x + 1) t1 (tred_shiftup_above 0 h))

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
    | TrFor #t1 #t2 k ht1 ->
      tsubst_gen_tlam x s k t1;
      tsubst_gen_tlam x s' k t2;
      TrFor k (subst_of_tred_tred (x + 1) (tred_shiftup_above 0 hs) ht1)

type ltup =
  | MkLTup: #s:typ -> #t:typ -> #u:typ -> (tred s t) -> (tred s u) -> ltup

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
      ExIntro (tsubst_beta_gen 0 v2 v1)
              (Conj (subst_of_tred_tred 0 p2a p1a)
                    (subst_of_tred_tred 0 p2b p1b))

    (* one TrBeta and other TrApp *)
    | MkLTup (TrBeta #s1 #s2 #t1' #t2' k h11 h12)
             (TrApp #s1' #s2' #lu1' #u2' h21 h22) ->
    (* AR: does not work without this type annotation *)
      let h21:(tred (TLam.t s1') (TLam.t lu1')) = match h21 with
      	| TrLam _ h' -> h'
      	| TrRefl _ -> TrRefl (TLam.t s1') in

      let ExIntro v1 (Conj p1a p1b) = tred_diamond h11 h21 in
      let ExIntro v2 (Conj p2a p2b) = tred_diamond h12 h22 in
    	let v = tsubst_beta_gen 0 v2 v1 in
    	ExIntro v (Conj (subst_of_tred_tred 0 p2a p1a) (TrBeta k p1b p2b))

    | MkLTup (TrApp #s1' #s2' #lu1' #u2' h21 h22)
             (TrBeta #s1 #s2 #t1' #t2' k h11 h12) ->
      let ExIntro v1 (Conj p1 p2)  = tred_diamond h21 (TrLam k h11) in
      let ExIntro v2 (Conj p3 p4)  = tred_diamond h22 h12 in

      let h_body:(tred (TLam.t lu1') (TLam.t v1)) = match p1 with
    	| TrLam _ h' -> h'
    	| TrRefl _ -> TrRefl (TLam.t lu1')
      in
      let h_body2:(tred t1' (TLam.t v1)) = match p2 with
    	| TrLam _ h' -> h'
    	| TrRefl _ -> TrRefl t1'
      in

      ExIntro (tsubst_beta v2 (TLam.t v1))
              (Conj (TrBeta k h_body p3) (subst_of_tred_tred 0 p4 h_body2))
    (* if one is TrFor, the other has to be TrFor *)
    | MkLTup (TrFor k h11) (TrFor _ h12) ->
    (* AR: p only has one constructor Conj,
           but direct pattern matching doesn't work *)
      let ExIntro t' (Conj pa pb) = tred_diamond h11 h12 in
      ExIntro (TFor k t') (Conj (TrFor k pa) (TrFor k pb))

type tred_star: typ -> typ -> Type =
  | TsRefl : t:typ ->
             tred_star t t

  | TsStep : #t1:typ -> #t2:typ -> #t3:typ ->
             tred      t1 t2 ->
             tred_star t2 t3 ->
             tred_star t1 t3

opaque val tred_star_one_loop: #s:typ -> #t:typ -> #u:typ ->
      h:(tred s t) -> hs:(tred_star s u) ->
      Tot (cexists (fun v -> cand (tred_star t v) (tred u v))) (decreases hs)
let rec tred_star_one_loop s t u h hs =
  match hs with
    | TsRefl _ ->
      ExIntro t (Conj (TsRefl t) h)
    | TsStep #s #u1 #u h1 hs' ->
      let ExIntro v1 p1 = tred_diamond h h1 in
      let Conj p1a p1b = p1 in
      let ExIntro v p2 = tred_star_one_loop p1b hs' in
      let Conj p2a p2b = p2 in
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
      let ExIntro v1 p = tred_star_one_loop h1' h2 in
      let Conj p1 p2 = p in
      let ExIntro v p' = confluence hs1 p1 in
      let Conj p1' p2' = p' in
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
             tred t1 t2 ->
             tred_star_sym t1 t2
  | TssSym: #t1:typ -> #t2:typ ->
            tred_star_sym t2 t1 ->
            tred_star_sym t1 t2
  | TssTran: #t1:typ -> #t2:typ -> #t3:typ ->
             tred_star_sym t1 t2 ->
             tred_star_sym t2 t3 ->
             tred_star_sym t1 t3

(* Proposition 30.3.10 in TAPL (has a graphical proof only for this, pg. 561) *)
opaque val tred_star_sym_confluent : #s:typ -> #t:typ ->
      h:tred_star_sym s t ->
      Tot (cexists (fun u -> cand (tred_star s u) (tred_star t u))) (decreases h)
let rec tred_star_sym_confluent s t h =
  match h with
    | TssBase h1 -> ExIntro t (Conj (TsStep h1 (TsRefl t)) (TsRefl t))
    | TssSym h1 ->
      let ExIntro u p = tred_star_sym_confluent h1 in
      let Conj p1 p2 = p in
      ExIntro u (Conj p2 p1)
    | TssTran #s #v #t h1 h2 ->
      let ExIntro u1 p = tred_star_sym_confluent h1 in
      let Conj psu1 pvu1 = p in
      let ExIntro u2 p = tred_star_sym_confluent h2 in
      let Conj pvu2 ptu2 = p in

      let ExIntro w p = confluence pvu1 pvu2 in
      let Conj pu1w pu2w = p in
      ExIntro w (Conj (ts_tran psu1 pu1w) (ts_tran ptu2 pu2w))

opaque val trlam_tss : #t1:typ -> #t2:typ -> k:knd ->
      h:(tred_star_sym t1 t2) ->
      Tot (tred_star_sym (TLam k t1) (TLam k t2)) (decreases h)
let rec trlam_tss t1 t2 k h =
  match h with
    | TssBase h1 -> TssBase (TrLam k h1)
    | TssSym h1 -> TssSym (trlam_tss k h1)
    | TssTran h1 h2 -> TssTran (trlam_tss k h1) (trlam_tss k h2)

opaque val trfor_tss : #t1:typ -> #t2:typ -> k:knd ->
      h:(tred_star_sym t1 t2) ->
      Tot (tred_star_sym (TFor k t1) (TFor k t2)) (decreases h)
let rec trfor_tss t1 t2 k h =
  match h with
    | TssBase h1 -> TssBase (TrFor k h1)
    | TssSym h1 -> TssSym (trfor_tss k h1)
    | TssTran h1 h2 -> TssTran (trfor_tss k h1) (trfor_tss k h2)

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
    | EqFor #t #t' k h1 -> TssTran (trfor_tss k (tequiv_tss h1))
      (TssBase (TrRefl (TFor k t')))

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
      EqTran (EqApp (EqLam k (tred_tequiv h1)) (tred_tequiv h2)) (EqBeta k t1' t2')
    | TrFor k h1 -> EqFor k (tred_tequiv h1)

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
    	  let ExIntro t1 p = tred_tarr_preserved #u1 #u2 #t hs1 in
    	  let ExIntro t2 p = p in
    	  let Conj p1 p2 = p in
    	  ExIntro t1 (ExIntro t2 (Conj (TsStep h11 p1) (TsStep h12 p2)))

opaque val tred_tfor_preserved: #k:knd -> #t1:typ -> #t:typ ->
                               h:tred_star (TFor k t1) t ->
	                       Tot (cexists (fun t' -> (u:(tred_star t1 t'){t = TFor k t'}))) (decreases h)
let rec tred_tfor_preserved k t1 t h =
  match h with
    | TsRefl _ -> ExIntro t1 (TsRefl t1)
    | TsStep #dc1 #s #dc2 h1 h2 ->
      (match h1 with
    	| TrRefl _ -> tred_tfor_preserved #k #t1 #t h2
    	| TrFor #dc1 #t1' dc2 h12 ->
    	  let ExIntro t' p = tred_tfor_preserved #k #t1' #t h2 in
    	  ExIntro t' (TsStep h12 p)
      )

(* TArr cannot be equivalent to TFor *)
opaque val arrow_eq_tfor_contra: #t1:typ -> #t2:typ -> #k:knd -> #t3:typ ->
                                 h:(tequiv (TArr t1 t2) (TFor k t3)) ->
                                 Tot (u:unit{false})
let arrow_eq_tfor_contra t1 t2 k t3 h =
  let ExIntro u p = tequiv_tred_tred h in
  let Conj p1 p2 = p in
  let ExIntro _ p1 = tred_tarr_preserved #t1 #t2 #u p1 in
  let ExIntro _ p2 = tred_tfor_preserved #k #t3 #u p2 in
  Classical.give_proof p1;
  Classical.give_proof p2

opaque val efor_typing_eq_tfor: #k:knd -> #e:exp -> #t:typ ->
                                h:typing empty (EForT k e) t ->
                                Tot (cexists (fun t1 -> tequiv t (TFor k t1))) (decreases h)
let rec efor_typing_eq_tfor k e t h =
  match h with
    | TyFor #dc1 #dc2 #t1 _ _ ->
      ExIntro t1 (EqRefl (TFor k t1))
    | TyEqu #dc1 #d2 #t1 #dc3 h1 h2 h3 ->
      let ExIntro t2 p = efor_typing_eq_tfor #k #e #t1 h1 in
      ExIntro t2 (EqTran (EqSymm h2) p)

opaque val elam_typing_eq_tarr: #t1:typ -> #e:exp -> #t:typ ->
                                h:typing empty (ELam t1 e) t ->
                                Tot (cexists (fun t2 -> tequiv t (TArr t1 t2))) (decreases h)
let rec elam_typing_eq_tarr t1 e t h =
  match h with
    | TyLam #dc _ #dc2 #t2 _ _ ->
      ExIntro t2 (EqRefl (TArr t1 t2))
    | TyEqu #dc1 #dc2 #t2 #dc3 h1 h2 h3 ->
      let ExIntro t3 p = elam_typing_eq_tarr #t1 #e #t2 h1 in
      ExIntro t3 (EqTran (EqSymm h2) p)

(* expression with type TArr cannot be a EForT, used in progress *)
opaque val tarr_not_efor: #e:exp -> #t1:typ -> #t2:typ ->
                          h:typing empty e (TArr t1 t2) ->
                          Tot (u:unit{(not (is_value e)) \/ is_ELam e})
let tarr_not_efor e t1 t2 h =
  match e with
    | EForT k e1 ->
      let ExIntro t3 p = efor_typing_eq_tfor #k #e1 #(TArr t1 t2) h in
      arrow_eq_tfor_contra #t1 #t2 #k #t3 p
    | _ -> ()

(* expression with type TFor cannot be a lambda, used in progress *)
opaque val fort_not_elam: #e:exp -> #k:knd -> #t1:typ ->
                          h:typing empty e (TFor k t1) ->
                          Tot (u:unit{(not (is_value e)) \/ is_EForT e})
let fort_not_elam e k t1 h =
  match e with
    | ELam t e1 ->
      let ExIntro t3 p = elam_typing_eq_tarr #t #e1 #(TFor k t1) h in
      arrow_eq_tfor_contra #t #t3 #k #t1 (EqSymm p)
    | _ -> ()

opaque val inversion_elam : #g:env -> s1:typ -> e:exp -> #s:typ -> t1:typ -> t2:typ ->
      ht:typing g (ELam s1 e) s -> heq:tequiv s (TArr t1 t2) ->
      hnew:kinding g t2 KTyp ->
      Tot (cand (cand (tequiv t1 s1) (typing (extend_evar g 0 s1) e t2))
                (kinding g s1 KTyp))  (decreases ht)
let rec inversion_elam g s1 e s t1 t2 ht heq hnew =
  match ht with
    | TyEqu #g #e' #u #s ht1 heq1 k1 ->
      inversion_elam s1 e t1 t2 ht1 (EqTran heq1 heq) hnew
    | TyLam #g s1 #e #s2 hk ht1 ->
      let ExIntro u p = tequiv_tred_tred heq in
      let Conj p1 p2 = p in

    (* implicits required *)
      let ExIntro u1 p = tred_tarr_preserved #s1 #s2 #u p1 in
      let ExIntro u2 p = p in
      let Conj psu1 psu2 = p in

    (* AR: implicits required *)
      let ExIntro u1' p = tred_tarr_preserved #t1 #t2 #u p2 in
      let ExIntro u2' p = p in
      let Conj ptu1 ptu2 = p in

    (*
     * AR: Cannot use Conj.pb directly below, have to let bind.
     *)

    (* AR: removing this type annotation, verification fails after taking a long time *)
    (* CH: I can reproduce this, even with z3timeout 100 I get:
       An unknown assertion in the term at this location was not provable *)
      let d1:(cand (kinding g s1 KTyp) (kinding g s2 KTyp)) =
    	kinding_inversion_arrow (typing_to_kinding ht) in
      let Conj pa pb = d1 in

      let pst2 = EqTran (tred_star_tequiv psu2) (EqSymm (tred_star_tequiv ptu2)) in
      let h:(typing (extend_evar g 0 s1) e t2) =
    	TyEqu ht1 pst2 (kinding_weakening_ebnd hnew 0 s1) in
      Conj (Conj (EqTran (tred_star_tequiv ptu1) (EqSymm (tred_star_tequiv psu1))) h) hk

opaque val kinding_efor_inversion: #k1:knd -> #t1:typ -> #k2:knd -> #t2:typ ->
                            h:tequiv (TFor k1 t1) (TFor k2 t2) ->
                            Tot (u:(tequiv t1 t2){k1 = k2}) (decreases h)
let rec kinding_efor_inversion k1 t1 k2 t2 h =
  let ExIntro u p = tequiv_tred_tred h in
  let Conj p1 p2 = p in
  let ExIntro t1' p1 = tred_tfor_preserved #k1 #t1 #u p1 in
  let ExIntro t2' p2 = tred_tfor_preserved #k2 #t2 #u p2 in
  EqTran (tred_star_tequiv #t1 #t1' p1) (EqSymm (tred_star_tequiv #t2 #t2' p2))

opaque val inversion_efor_jk:#g:env ->#k1:knd -> #k2:knd -> #e:exp -> #s:typ -> #t:typ ->
                          h1:typing g (EForT k1 e) s ->
                          h2:tequiv s (TFor k2 t)    ->
                          Tot (u:unit{k1 = k2}) (decreases h1)
let rec inversion_efor_jk g k1 k2 e s t h1 h2 =
  match h1 with
    | TyFor #g' #e' #t' k1' h11 ->
      let _ = kinding_efor_inversion #k1 #t' #k2 #t h2 in
      ()
    | TyEqu #dc1 #dc2 #t' #dc3 h11 h12 h23 ->
      inversion_efor_jk #g #k1 #k2 #e #t' #t h11 (EqTran h12 h2)

opaque val inversion_efor:#g:env ->#k1:knd -> #k2:knd -> #e:exp -> #s:typ -> #t:typ ->
                          h1:typing g (EForT k1 e) s ->
                          h2:tequiv s (TFor k2 t)    ->
	                  hnew:kinding (extend_tvar g 0 k1) t KTyp      ->
                          Tot (u:(typing (extend_tvar g 0 k1) e t){k1 = k2}) (decreases h1)
let rec inversion_efor g k1 k2 e s t h1 h2 hnew =
  match h1 with
    | TyFor #g' #e' #t' k1' h11 ->
      let p = kinding_efor_inversion #k1 #t' #k2 #t h2 in
      TyEqu h11 p hnew
    | TyEqu #dc1 #dc2 #t' #dc3 h11 h12 h23 ->
      inversion_efor #g #k1 #k2 #e #t' #t h11 (EqTran h12 h2) hnew

(* Corollary of inversion_elam *)
opaque val inversion_elam_typing : #g:env -> s1:typ -> e:exp ->
      t1:typ -> t2:typ -> typing g (ELam s1 e) (TArr t1 t2) ->
      Tot (cand (cand (tequiv t1 s1) (typing (extend_evar g 0 s1) e t2))
                (kinding g s1 KTyp))
let inversion_elam_typing g s1 e t1 t2 h =
  let Conj _ hnew = kinding_inversion_arrow #g #t1 #t2
                      (typing_to_kinding h) in
  inversion_elam s1 e t1 t2 h (EqRefl (TArr t1 t2)) hnew

opaque val inversion_efor_typing: #g:env -> #k1:knd -> #e:exp -> #k2:knd -> #t:typ ->
                                  h:typing g (EForT k1 e) (TFor k2 t) ->
                                  Tot (u:(typing (extend_tvar g 0 k1) e t){k1 = k2})
                                  (decreases h)
let rec inversion_efor_typing g k1 e k2 t h =
  let p = kinding_inversion_forall #g #k2 #t (typing_to_kinding #g #(EForT k1 e) #(TFor k2 t) h) in
  let _ = inversion_efor_jk #g #k1 #k2 #e #(TFor k2 t) #t h (EqRefl (TFor k2 t)) in
  inversion_efor #g #k1 #k2 #e #(TFor k2 t) #t h (EqRefl (TFor k2 t)) p

(* Progress *)
opaque val progress : #e:exp -> #t:typ -> h:typing empty e t ->
               Pure (cexists (fun e' -> step e e'))
                    (requires (not (is_value e)))
                    (ensures (fun _ -> True)) (decreases h)
let rec progress _ _ h =
  match h with
    | TyApp #g #e1 #e2 #t11 #t12 h1 h2 ->
      tarr_not_efor #e1 #t11 #t12 h1;
      (match e1 with
       | ELam t e1' -> ExIntro (esubst_beta e2 e1') (SBeta t e1' e2)
       | _ ->
         match progress h1 with
           | ExIntro e1' h1' -> ExIntro (EApp e1' e2) (SApp1 e2 h1'))
    | TyEqu h1 _ _ -> progress h1

    | TyAppT #g #e #t #k #t' h1 hk ->
      fort_not_elam #e #t' #k h1;
      (match e with
    	| EForT k e1 -> ExIntro (esubst_tbeta t e1) (SBetaT k e1 t)
    	| _ ->
    	  let ExIntro e' h2 = progress h1 in
    	  ExIntro (ETApp e' t) (STApp1 t h2)
      )

(* Type preservation *)
opaque val preservation : #e:exp -> #e':exp -> hs:step e e' ->
                   #g:env -> #t:typ -> ht:(typing g e t) ->
                   Tot (typing g e' t) (decreases ht)
let rec preservation _ _ hs _ _ ht =
  match ht with
  | TyApp #g #e1 #e2 #t1 #t2 h1 h2 ->
    (match hs with
     | SBeta s1 e11 e12 ->
       let Conj p12 (p3:kinding g s1 KTyp) = inversion_elam_typing s1 e11 t1 t2 h1 in
       let Conj (p1:tequiv t1 s1) (p2:typing (extend_evar g 0 s1) e11 t2) = p12 in
       typing_substitution 0 (TyEqu h2 p1 p3) p2
     | SApp1 e2' hs1   -> TyApp (preservation hs1 h1) h2
     | SApp2 e1' hs2   -> TyApp h1 (preservation hs2 h2))
  | TyEqu ht1 he hk -> TyEqu (preservation hs ht1) he hk
  | TyAppT #g #e' #t' #t1' k1 ht1 ht2 ->
    (match hs with
      | SBetaT k2 e'' dc1 ->
	let p = inversion_efor_typing #g #k2 #e'' #k1 #t1' ht1 in
	typing_substitution_t 0 #e'' #t' #k1 #t1' #g ht2 p
      | STApp1 #dc1 #e'' #dc2 hs1 ->
	TyAppT #g #e'' #t' #t1' k1 (preservation #e' #e'' hs1 #g #(TFor k1 t1') ht1) ht2
    )
