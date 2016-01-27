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


module Bob
open FStar.Bytes
open Crypto_interface
open Assumptions

(* -------------- Bob Interface -------------- *)
val bob : pub_id_t ->
         cb:cipher{(FromBboth (fst cb) (snd cb)) /\ (exists (mLb:bytes) (mRb:bytes).((Encryptedboth mLb mRb (fst cb) (snd cb)) /\ (Marshboth (fst v2) (snd v1) mLb mRb)))}
