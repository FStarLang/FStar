(*--build-config
    other-files:FStar.Int8.fst
 --*)

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
