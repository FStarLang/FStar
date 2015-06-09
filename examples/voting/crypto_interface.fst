(*
   Copyright 2015 Chantal Keller, Microsoft Research and Inria

   Based on work by V. Cortier, F. Eigner, S. Kremer, M. Maffei and C.
   Wiedling <https://sps.cs.uni-saarland.de/voting>.

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


module Crypto_interface
open Comp
(* open Heap *)
open Bytes


(* -------------- Programming Assumptions and TODO List -------------- *)

(* -------------- Eq Types -------------- *)
type twice (a:Type) = a * a

val same : 'a -> Tot (twice 'a)
let same x = (x,x)

type tbytes = twice bytes
type tint = twice int
type tbool = twice bool

type eq 'a = x:(twice 'a){fst x = snd x}

val pair_map2 : ('a -> 'b -> Tot 'c) -> (twice 'a) -> (twice 'b) -> Tot (twice 'c)
let pair_map2 f (x1,x2) (y1,y2) = (f x1 y1, f x2 y2)

(* -------------- Specified constants -------------- *)
type vote = eq int
assume val v1:vote
assume val v2:vote

(* -------------- Types Definitions -------------- *)
type cipher = eq bytes

(* -------------- Predicates Definitions -------------- *)
assume type Encrypted : bytes -> bytes -> Type
assume type Encryptedboth : bytes -> bytes -> bytes -> bytes -> Type
(* Note: We define a "both" version of predicates for writing purposes. *)

type FromA : bytes -> Type
type FromAboth : bytes -> bytes -> Type

type FromB : bytes -> Type
type FromBboth : bytes -> bytes -> Type

type FromO : bytes -> Type
type FromOboth : bytes -> bytes -> Type

type Marsh : int -> bytes -> Type
type Marshboth : int -> int -> bytes -> bytes -> Type

type Valid : bytes -> Type
type Validboth : bytes -> bytes -> Type

(* -------------- Macros -------------- *)
assume val hypEncrypted :
    (m:bytes) -> (n:bytes) -> (x:bytes) -> (y:bytes) -> Lemma
         (requires True)
         (ensures ((Encryptedboth m n x y) <==> ((Encrypted m x) /\ (Encrypted n y)))) [SMTPatT (Encryptedboth m n x y)]
assume val hypFromA :
    (x:bytes) -> (y:bytes) -> Lemma
         (requires True)
         (ensures (FromAboth x y <==> ((FromA x) /\ (FromA y)))) [SMTPatT (FromAboth x y)]
assume val hypFromB :
    (x:bytes) -> (y:bytes) -> Lemma
         (requires True)
         (ensures (FromBboth x y <==> ((FromB x) /\ (FromB y)))) [SMTPatT (FromBboth x y)]
assume val hypFromO :
    (x:bytes) -> (y:bytes) -> Lemma
         (requires True)
         (ensures (FromOboth x y <==> ((FromO x) /\ (FromO y)))) [SMTPatT (FromOboth x y)]
assume val hypMarsh :
    (m:int) -> (n:int) -> (x:bytes) -> (y:bytes) -> Lemma
         (requires True)
         (ensures ((Marshboth m n x y) <==> ((Marsh m x) /\ (Marsh n y)))) [SMTPatT (Marshboth m n x y)]
assume val hypValid :
    (x:bytes) -> (y:bytes) -> Lemma
         (requires True)
         (ensures (Validboth x y <==> ((Valid x) /\ (Valid y)))) [SMTPatT (Validboth x y)]

(* -------------- Marshalling -------------- *)
(* Marshalling Assumptions *)
assume val marshInj1 :
    (z1:int) -> (z2:int) -> (m:bytes) -> Lemma
         (requires True)
         (ensures (((Marsh z1 m) /\ (Marsh z2 m)) ==> (z1 = z2))) [SMTPatT (Marsh z1 m); SMTPatT (Marsh z2 m)]
assume val marshInj2 :
    (z:int) -> (m1:bytes) -> (m2:bytes) -> Lemma
         (requires True)
         (ensures (((Marsh z m1) /\ (Marsh z m2)) ==> (m1 = m2))) [SMTPatT (Marsh z m1); SMTPatT (Marsh z m2)]

(* Marshalling Functions *)
assume val i2b: x:(eq int) -> y:tbytes{Marshboth (fst x) (snd x) (fst y) (snd y)}
assume val b2i: x:bytes -> y:int{Marsh y x}

(* -------------- Seal for randomized asymmetric encryption (simple decryption) -------------- *)
(* Seal reference for T(able) All *)
type seal_ref_entry_t = mc:(tbytes * cipher){Encryptedboth (fst (fst mc)) (snd (fst mc)) (fst (snd mc)) (snd (snd mc))}
type seal_ref_list_t = list seal_ref_entry_t
type seal_ref_t = ref seal_ref_list_t

(* Seal reference for T(able) Valid *)
type seal_val_ref_entry_t =
  mc:(tbytes * cipher)
    {Encryptedboth (fst (fst mc)) (snd (fst mc)) (fst (snd mc)) (snd (snd mc))
     /\ (Validboth (fst (snd mc)) (snd (snd mc)) )
     /\ ((FromAboth (fst (snd mc)) (snd (snd mc))) \/ (FromBboth (fst (snd mc)) (snd (snd mc)))
	                         \/ ((FromOboth (fst (snd mc)) (snd (snd mc))) /\ (fst (fst mc) = snd (fst mc))))
     /\ (exists (zL:int) (zR:int).(Marshboth zL zR (fst (fst mc)) (snd (fst mc))))}
(* Note: seal_fun_O_t will need to check that input is marsh of an int (v1 or v2). *)

type seal_val_ref_list_t = list seal_val_ref_entry_t
type seal_val_ref_t = ref seal_val_ref_list_t

(* Leave title here *)
type seal_both_ref_t = seal_ref_t * seal_val_ref_t

(* Sealing functions types for T(able) all and valid *)
type seal_fun_A_t = m:tbytes{(Marsh (fst v1) (fst m)) /\ (Marsh (snd v2) (snd m))} ->
    c:cipher{(Encryptedboth (fst m) (snd m) (fst c) (snd c)) /\ (FromAboth (fst c) (snd c))}
(* does: new c.assume (FromAboth (L c) (R c)) && (Encrypted m c) && (Valid c) store (m,c) in both tables *)

assume val seal_fun_A: seal_both_ref_t -> seal_fun_A_t

type seal_fun_B_t =
  m:tbytes{(Marsh (fst v2) (fst m)) /\ (Marsh (snd v1) (snd m))} ->
    c:cipher{(Encryptedboth (fst m) (snd m) (fst c) (snd c)) /\ (FromBboth (fst c) (snd c))}

assume val seal_fun_B: seal_both_ref_t -> seal_fun_B_t

type seal_fun_O_t = m:(eq bytes) -> cipher

assume val seal_fun_O: seal_both_ref_t -> seal_fun_O_t

(* Unseal function type for T(able) all (will be used for decryption) *)
type unseal_fun_t = c:cipher -> option (m:tbytes{forall (z1:bytes) (z2:bytes). ((Encryptedboth z1 z2 (fst c) (snd c)) ==> ((z1 = fst m) /\ (z2 = snd m)))})
(* Note: Should be an option type *)

assume val unseal_fun: seal_both_ref_t -> unseal_fun_t

(* Unseal function type for T(able) valid (used for validity checks) *)
type unseal_val_fun_t = c:cipher -> b:bool{(b = true) ==> (
                        (Validboth (fst c) (snd c))
						/\ (exists (m1:bytes) (m2:bytes) (z1:int) (z2:int).(
							(Encryptedboth m1 m2 (fst c) (snd c)) /\ (Marshboth z1 z2 m1 m2)
							/\ ( ( (FromAboth (fst c) (snd c)) )
								\/ ( (FromBboth (fst c) (snd c)) )
								\/ ( (FromOboth (fst c) (snd c)) /\ (m1 = m2) ) ))))}

assume val unseal_val_fun: seal_both_ref_t -> unseal_val_fun_t

(* Reseal function type for homomorphic encryption *)
type reseal_hom_fun_t = c1:cipher -> c2:cipher -> c:cipher{forall (mL1:bytes) (mL2:bytes) (mR1:bytes) (mR2:bytes)
							(zL1:int) (zL2:int) (zR1:int) (zR2:int).(
					( (Encryptedboth mL1 mR1 (fst c1) (snd c1)) /\ (Encryptedboth mL2 mR2 (fst c2) (snd c2))
					/\ (Marshboth zL1 zR1 mL1 mR1) /\ (Marshboth zL2 zR2 mL2 mR2) )
                    ==> (exists (mL:bytes) (mR:bytes).(
						(Encryptedboth mL mR (fst c) (snd c)) /\ (Marshboth (zL1 + zL2) (zR1 + zR2) mL mR))))}

assume val reseal_hom_fun: seal_both_ref_t -> reseal_hom_fun_t

(* Leave title here *)
type pub_id_t = eq bytes
type priv_id_t = int
type pub_comp_t = seal_fun_A_t * seal_fun_B_t * seal_fun_O_t * unseal_val_fun_t * reseal_hom_fun_t
type priv_comp_t = unseal_fun_t
type keylist_entry_t = (pub_id_t * priv_id_t) * (pub_comp_t * priv_comp_t)
type keylist_t = list keylist_entry_t
type key_ref_t = ref keylist_t

(* Waiting to figure out how ref is working *)
assume val mkKeyRef: unit -> key_ref_t

(* Leave title here *)
type mkSeal_fun_t = unit -> (pub_comp_t * priv_comp_t)
assume val mkSeal:mkSeal_fun_t

type mkPrivKey_fun_t = key_ref_t -> unit -> priv_id_t
assume val mkPrivKey:mkPrivKey_fun_t

type mkPubKey_fun_t = key_ref_t -> priv_id_t -> pub_id_t
assume val mkPubKey:mkPubKey_fun_t

(* Leave title here *)
assume val encA: pub_id_t -> seal_fun_A_t

assume val encB: pub_id_t -> seal_fun_B_t

assume val encO: pub_id_t -> seal_fun_O_t

assume val check_val: pub_id_t -> unseal_val_fun_t

assume val hom_add: pub_id_t -> reseal_hom_fun_t

assume val dec: priv_id_t -> unseal_fun_t
