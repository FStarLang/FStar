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


module Protocol
open FStar.Bytes
open Crypto_interface
open Assumptions
open Alice
open Bob
open Ballot_box

(* -------------- Types for the Protocol -------------- *)
(* Note: In the end, the protocol should have type eq bytes -> eq bytes *)

type in_P1_t = eq bytes
type in_P2_t = eq bytes
type in_P3_t = cipher
type out_P3_t = result
type out_P2_t = ( cipher * (in_P3_t -> out_P3_t) )
type out_P1_t = ( cipher * (in_P2_t -> out_P2_t) )

(* -------------- Protocol ------------- *)

val p1: error -> in_P1_t -> out_P1_t
let p1 e arg1 =
  let key_ref = mkKeyRef () in
  let skBB = mkPrivKey key_ref () in
  let pkBB = mkPubKey key_ref skBB in
  let cA = alice pkBB in

  let p2 arg2 : out_P2_t =
    let cB = bob pkBB in

    let p3 cO =
      let res = ballotBox pkBB skBB cA cB cO e in
      res in

    (cB,p3) in

  (cA,p2)
