module TestInt63
open Int63
let f0 (x:nat63) : int63 = x - 1l
let f1 (x:nat63) (y:nat63{y <= x}) : nat63 = x - y
let f2 (x:nat63{x < (Int63.max_value / 2l)}) = x * 2l
let mid_nat (x:nat63) (y:nat63{y <= x /\ y<>0l}) : nat63 =
  x - ((x - y) / 2l)
let max (x:int63) (y:int63) = if x < y then y else x
let min (x:int63) (y:int63) = if x < y then x else y

//possibly overflowing versions
let g0 (x:int63) = x ?- 1l
let g1 (x:int63) (y:int63) : int63 = x ?- y
let g2 (x:int63) = x ?* 2l
let mid_nat' (x:nat63) (y:nat63) : int63 = (x ?+ y) ?/ 2l
let times' (x:int63) = x ?* 2l

val lemma_g0_f0 : x:nat63 -> Lemma (ensures (f0 x = g0 x))
let lemma_g0_f0 x = ()

val lemma_g1_f1 : x:nat63 -> y:nat63{y <= x} -> Lemma (ensures (f1 x y = g1 x y))
let lemma_g1_f1 x y = ()

val lemma_g2_f2 : x:nat63{x < (Int63.max_value / 2l)} -> Lemma (ensures (f2 x = g2 x))
let lemma_g2_f2 x = ()

val lemma_mid'_mid : x:nat63 -> y:nat63{y <= x /\ y<>0l}
                -> Lemma
                  (requires ((Prims.op_LessThanOrEqual (Prims.op_Addition (as_int x) (as_int y))
                                                       Int63.max_value_int)
                             /\ ((x + y) % 2l) = 0l))
                  (ensures (mid_nat x y = mid_nat' x y))
let lemma_mid'_mid x y = ()
