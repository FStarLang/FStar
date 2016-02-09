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


module Alice
open FStar.Bytes
open Crypto_interface
open Assumptions

val alice : pub_id_t ->
         ca:cipher{(FromAboth (fst ca) (snd ca)) /\ (exists (mLa:bytes) (mRa:bytes).((Encryptedboth mLa mRa (fst ca) (snd ca)) /\ (Marshboth (fst v1) (snd v2) mLa mRa)))}
let alice pkBB =
  let v1Byt = i2b v1 in
  let v2Byt = i2b v2 in
  let va = choice v1Byt v2Byt in
  let ca = encA pkBB va in
  ca
