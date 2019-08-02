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
module TestInt8
open FStar.Int8
let f0 (x:nat8) : int8 = x - 1y
let f1 (x:nat8) (y:nat8{y <= x}) : nat8 = x - y
let f2 (x:nat8{x < (Int8.max_value / 2y)}) = x * 2y
let mid_nat (x:nat8) (y:nat8{y <= x /\ y<>0y}) : nat8 =
  x - ((x - y) / 2y)
let max (x:int8) (y:int8) = if x < y then y else x
let min (x:int8) (y:int8) = if x < y then x else y

//possibly overflowing versions
let g0 (x:int8) = x ?- 1y
let g1 (x:int8) (y:int8) : int8 = x ?- y
let g2 (x:int8) = x ?* 2y
let mid_nat' (x:nat8) (y:nat8) : int8 = (x ?+ y) ?/ 2y
let times' (x:int8) = x ?* 2y

val lemma_g0_f0 : x:nat8 -> Lemma (ensures (f0 x = g0 x))
let lemma_g0_f0 x = ()

val lemma_g1_f1 : x:nat8 -> y:nat8{y <= x} -> Lemma (ensures (f1 x y = g1 x y))
let lemma_g1_f1 x y = ()

val lemma_g2_f2 : x:nat8{x < (Int8.max_value / 2y)} -> Lemma (ensures (f2 x = g2 x))
let lemma_g2_f2 x = ()

val lemma_mid'_mid : x:nat8 -> y:nat8{y <= x /\ y<>0y}
                -> Lemma
                  (requires ((Prims.op_LessThanOrEqual (Prims.op_Addition (as_int x) (as_int y))
                                                       Int8.max_value_int)
                             /\ ((x + y) % 2y) = 0y))
                  (ensures (mid_nat x y = mid_nat' x y))
let lemma_mid'_mid x y = ()
