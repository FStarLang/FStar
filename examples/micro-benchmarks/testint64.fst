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
module TestInt64
open Int64
let f0 (x:nat64) : int64 = x - 1L
let f1 (x:nat64) (y:nat64{y <= x}) : nat64 = x - y
let f2 (x:nat64{x < (Int64.max_value / 2L)}) = x * 2L
let mid_nat (x:nat64) (y:nat64{y <= x /\ y<>0L}) : nat64 =
  x - ((x - y) / 2L)
let max (x:int64) (y:int64) = if x < y then y else x
let min (x:int64) (y:int64) = if x < y then x else y

//possibly overflowing versions
let g0 (x:int64) = x ?- 1L
let g1 (x:int64) (y:int64) : int64 = x ?- y
let g2 (x:int64) = x ?* 2L
let mid_nat' (x:nat64) (y:nat64) : int64 = (x ?+ y) ?/ 2L
let times' (x:int64) = x ?* 2L

val lemma_g0_f0 : x:nat64 -> Lemma (ensures (f0 x = g0 x))
let lemma_g0_f0 x = ()

val lemma_g1_f1 : x:nat64 -> y:nat64{y <= x} -> Lemma (ensures (f1 x y = g1 x y))
let lemma_g1_f1 x y = ()

val lemma_g2_f2 : x:nat64{x < (Int64.max_value / 2L)} -> Lemma (ensures (f2 x = g2 x))
let lemma_g2_f2 x = ()

val lemma_mid'_mid : x:nat64 -> y:nat64{y <= x /\ y<>0L}
                -> Lemma
                  (requires ((Prims.op_LessThanOrEqual (Prims.op_Addition (as_int x) (as_int y))
                                                       Int64.max_value_int)
                             /\ ((x + y) % 2L) = 0L))
                  (ensures (mid_nat x y = mid_nat' x y))
let lemma_mid'_mid x y = ()
