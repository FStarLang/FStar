(*--build-config
    other-files:../../lib/int64.fst
 --*)

module TestInt64
open Int64
let f0 (x:nat64) : int64 = x - 1l
let f1 (x:nat64) (y:nat64{y <= x}) : nat64 = x - y
let f2 (x:nat64{x < (Int64.max_value / 2l)}) = x * 2l
let mid_nat (x:nat64) (y:nat64{y <= x /\ y<>0l}) : nat64 =
  x - ((x - y) / 2l)
let max (x:int64) (y:int64) = if x < y then y else x
let min (x:int64) (y:int64) = if x < y then x else y

//possibly overflowing versions
let g0 (x:int64) = x ?- 1l
let g1 (x:int64) (y:int64) : int64 = x ?- y
let g2 (x:int64) = x ?* 2l
let mid_nat' (x:nat64) (y:nat64) : int64 = (x ?+ y) ?/ 2l
let times' (x:int64) = x ?* 2l

val lemma_g0_f0 : x:nat64 -> Lemma (ensures (f0 x = g0 x))
let lemma_g0_f0 x = ()

val lemma_g1_f1 : x:nat64 -> y:nat64{y <= x} -> Lemma (ensures (f1 x y = g1 x y))
let lemma_g1_f1 x y = ()

val lemma_g2_f2 : x:nat64{x < (Int64.max_value / 2l)} -> Lemma (ensures (f2 x = g2 x))
let lemma_g2_f2 x = ()

val lemma_mid'_mid : x:nat64 -> y:nat64{y <= x /\ y<>0l}
                -> Lemma
                  (requires ((Prims.op_LessThanOrEqual (Prims.op_Addition (as_int x) (as_int y))
                                                       Int64.max_value_int)
                             /\ ((x + y) % 2l) = 0l))
                  (ensures (mid_nat x y = mid_nat' x y))
let lemma_mid'_mid x y = ()
