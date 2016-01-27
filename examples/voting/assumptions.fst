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


module Assumptions
open FStar.Bytes
open Crypto_interface

(* -------------- Global Types -------------- *)
type error = eq bytes
type result = eq bytes

(* -------------- Global Functions -------------- *)
assume val choice : x:eq bytes -> y:eq bytes -> v:tbytes{(fst v = fst x) /\ (snd v = snd y)}

(* -------------- Global Assumptions -------------- *)
(* A single ciphertext only corresponds to one plaintext *)
assume val encryptedInj : (mL1:bytes) -> (mL2:bytes) -> (mR1:bytes) -> (mR2:bytes) -> (c1:bytes) -> (c2:bytes) -> Lemma
         (requires True)
         (ensures ((Encryptedboth mL1 mR1 c1 c2) /\ (Encryptedboth mL2 mR2 c1 c2)) ==> ((mL1 = mL2) /\ (mR1 = mR2)))
         [SMTPatT (Encryptedboth mL1 mR1 c1 c2); SMTPatT (Encryptedboth mL2 mR2 c1 c2)]

(* Voter A only vote once. *)
assume val aVotesOnce : (c1:bytes) -> (c2:bytes) -> Lemma
         (requires True)
         (ensures (((FromA c1) /\ (FromA c2)) ==> (c1 = c2))) [SMTPatT (FromA c1); SMTPatT (FromA c2)]

(* Voter B only vote once. *)
assume val bVotesOnce: (c1:bytes) -> (c2:bytes) -> Lemma
         (requires True)
         (ensures (((FromB c1) /\ (FromB c2)) ==> (c1 = c2))) [SMTPatT (FromB c1); SMTPatT (FromB c2)]
