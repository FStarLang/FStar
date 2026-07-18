module BoxBitVec
module BV = FStar.BV
open FStar.BV
let test (x:BV.bv_t 3) = BV.bvdiv x 1
let bv_trivial (input_x : BV.bv_t 3) = assert (BV.bvdiv input_x 1 == input_x)
