(*--build-config
    other-files:../../lib/FStar.Int16.fst
 --*)

module TestInt16
open Int16
let f0 (x:nat16) : int16 = x - 1s
let f1 (x:nat16) (y:nat16{y <= x}) : nat16 = x - y
let f2 (x:nat16{x < (Int16.max_value / 2s)}) = x * 2s
let mid_nat (x:nat16) (y:nat16{y <= x /\ y<>0s}) : nat16 =
  x - ((x - y) / 2s)
let max (x:int16) (y:int16) = if x < y then y else x
let min (x:int16) (y:int16) = if x < y then x else y

//possibly overflowing versions
let g0 (x:int16) = x ?- 1s
let g1 (x:int16) (y:int16) : int16 = x ?- y
let g2 (x:int16) = x ?* 2s
let mid_nat' (x:nat16) (y:nat16) : int16 = (x ?+ y) ?/ 2s
let times' (x:int16) = x ?* 2s

val lemma_g0_f0 : x:nat16 -> Lemma (ensures (f0 x = g0 x))
let lemma_g0_f0 x = ()

val lemma_g1_f1 : x:nat16 -> y:nat16{y <= x} -> Lemma (ensures (f1 x y = g1 x y))
let lemma_g1_f1 x y = ()

val lemma_g2_f2 : x:nat16{x < (Int16.max_value / 2s)} -> Lemma (ensures (f2 x = g2 x))
let lemma_g2_f2 x = ()

val lemma_mid'_mid : x:nat16 -> y:nat16{y <= x /\ y<>0s}
                -> Lemma
                  (requires ((Prims.op_LessThanOrEqual (Prims.op_Addition (as_int x) (as_int y))
                                                       Int16.max_value_int)
                             /\ ((x + y) % 2s) = 0s))
                  (ensures (mid_nat x y = mid_nat' x y))
let lemma_mid'_mid x y = ()
