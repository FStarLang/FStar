module TestBV

open FStar.UInt
open FStar.Tactics
open FStar.Tactics.BV
module U = FStar.UInt32

let test0 (x y: U.t) =
  assert_by_tactic (U.add x y == U.add y x) (bv_tac ())



bvadd (int2bv (v x)) (int2bv (v y))
---------------------------------------------
add (v x) (v y) == add (v y) (v x)
----------------------------------------------
Mk (add (v x) (v y)) == Mk (add (v y) (v x))

let test1 (x y: uint_t 64) =
    assert_by_tactic (logand #64 x y == logand #64 y x)
                     (bv_tac ())

let test2 (x y : uint_t 64) = 
    assert_by_tactic (logand #64 (logand #64 x y) y == logand #64 y (logand #64 y x))
                     (bv_tac ())

let test3 (x y : uint_t 64) = 
    assert_by_tactic (logand #64 (logand #64 (logand #64 x y) x) y == logand #64 y (logand #64 x (logand #64 y x)))
                     (bv_tac ())

let test4 (x y : uint_t 64) = 
    assert_by_tactic (logand #64 (logand #64 x (logxor #64 x y)) y == logand #64 y (logand #64 x (logxor #64 y x)))
                     (bv_tac ())
//cannot prove
(* let test5 (x : uint_t 32) = *)
(*     assert_by_tactic (shift_left #32 x 3 == shift_left #32 (shift_left #32 x 2) 1) *)
(*                      (prune "";; addns "Prims";; bv_tac ()) *)
