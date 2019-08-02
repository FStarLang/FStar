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
module Bug1572
open FStar.Integers

[@(expect_failure [114])] //ill-typed pattern
let test (x:uint_64) =
  match x with
  | 0ul -> 0
  | _ -> 1

let test2 (x: (uint_64 & uint_32)) : nat =
  match x with //nested patterns with machine int constants
  | 0uL, 0ul -> 0
  | 1uL, 1ul -> 1
  | _ -> 2

let f (i:FStar.UInt8.t) = if i = 0x00uy then 0x00uy else 0x01uy

[@(expect_failure [19])] //incomplete patterns
let bad_lemma (i:FStar.UInt8.t) : Lemma (f i = 0x00uy) =
  match i with
  | 0x00uy -> assert_norm (f 0x00uy = 0x00uy)
