(*
   Copyright 2008-2018 Microsoft Research

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
module UnifyRefs

unfold let pow2_32 = 0x100000000
unfold let pow2_64 = 0x10000000000000000

let natN (n:nat) = x:nat{x < n}
let nat32 = natN pow2_32
let nat64 = natN pow2_64

(* Some history:
   These tests used to fail but they no longer do
   They exercise issues related to #606.
   See also bug-reports/bug606.fst
*)
let nat32_to_nat64'0 (n:nat32) : nat64 = n

let nat32_to_nat64'1 (n:natN pow2_32) : nat64 = n

let nat32_to_nat64'2 (n:nat32) : natN pow2_64 = n

let nat32_to_nat64'3 (n:natN pow2_32) : natN pow2_64 = n

let nat64_to_nat32'0 (n:nat64 {n < pow2_32}) : nat32 = n

let nat64_to_nat32'1 (n:nat64 {n < pow2_32}) : natN pow2_32 = n

let nat64_to_nat32'2 (n:natN pow2_64 {n < pow2_32}) : nat32 = n

let nat64_to_nat32'3 (n:natN pow2_64 {n < pow2_32}) : natN pow2_32 = n

(* Unfolding manually causes the unifier to do more work, and succeed
   But, it's no longer needed. *)

let nat32_to_nat64'4 (n:nat{n < pow2_32}) : natN pow2_64 = n

let nat32_to_nat64'5 (n:nat32) : (x:nat{x < pow2_64}) = n

let nat64_to_nat32'4 (n:(x:nat{x < pow2_64}) {n < pow2_32}) : nat32 = n

let nat64_to_nat32'5 (n:nat64 {n < pow2_32}) : (n:nat{n < pow2_32}) = n
