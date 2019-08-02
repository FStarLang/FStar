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
module TestInt31
open Int31
let f0 (x:nat31) : int31 = x - 1l
let f1 (x:nat31) (y:nat31{y <= x}) : nat31 = x - y
let f2 (x:nat31{x < (Int31.max_value / 2l)}) = x * 2l
let mid_nat (x:nat31) (y:nat31{y <= x /\ y<>0l}) : nat31 =
  x - ((x - y) / 2l)
let max (x:int31) (y:int31) = if x < y then y else x
let min (x:int31) (y:int31) = if x < y then x else y

//possibly overflowing versions
let g0 (x:int31) = x ?- 1l
let g1 (x:int31) (y:int31) : int31 = x ?- y
let g2 (x:int31) = x ?* 2l
let mid_nat' (x:nat31) (y:nat31) : int31 = (x ?+ y) ?/ 2l
let times' (x:int31) = x ?* 2l

val lemma_g0_f0 : x:nat31 -> Lemma (ensures (f0 x = g0 x))
let lemma_g0_f0 x = ()

val lemma_g1_f1 : x:nat31 -> y:nat31{y <= x} -> Lemma (ensures (f1 x y = g1 x y))
let lemma_g1_f1 x y = ()

val lemma_g2_f2 : x:nat31{x < (Int31.max_value / 2l)} -> Lemma (ensures (f2 x = g2 x))
let lemma_g2_f2 x = ()

val lemma_mid'_mid : x:nat31 -> y:nat31{y <= x /\ y<>0l}
                -> Lemma
                  (requires ((Prims.op_LessThanOrEqual (Prims.op_Addition (as_int x) (as_int y))
                                                       Int31.max_value_int)
                             /\ ((x + y) % 2l) = 0l))
                  (ensures (mid_nat x y = mid_nat' x y))
let lemma_mid'_mid x y = ()
