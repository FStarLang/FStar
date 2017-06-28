module TestBV

open FStar.UInt
open FStar.Tactics
open FStar.Tactics.BV


let test1 (x y: uint_t 64) =
assert_by_tactic (bv_tac ()) (logand #64 x y == logand #64 y x)
let test2 (x y : uint_t 64) = 
  assert_by_tactic (bv_tac ()) (logand #64 (logand #64 x y) y == logand #64 y (logand #64 y x))
let test3 (x y : uint_t 64) = 
  assert_by_tactic (bv_tac ()) 
  (logand #64 (logand #64 (logand #64 x y) x) y == logand #64 y (logand #64 x (logand #64 y x)))
let test4 (x y : uint_t 64) = 
  assert_by_tactic (bv_tac ()) 
  (logand #64 (logand #64 x (logxor #64 x y)) y == logand #64 y (logand #64 x (logxor #64 y x)))
//canot prove
// let test5 (x : uint_t 32) =
//   assert_by_tactic (prune "";; addns "Prims";; bv_tac ())
//     (shift_left #32 x 3 == shift_left #32 (shift_left #32 x 2) 1)
