module IntBV

open FStar.UInt
open FStar.BV

[@@coercion]
let int_to_bv1 (#n : pos) (x : int) : Pure (BV.bv_t n) (requires fits x n) (ensures fun _ -> True)  = BV.int2bv x

let test1 : BV.bv_t 2 = 1
let test2 : BV.bv_t 3 = 1
let test3 : BV.bv_t 4 = 1

[@@expect_failure [66]] (* Failed to resolve implicit *)
let test4 : BV.bv_t _ = 1

let test5 = 1
