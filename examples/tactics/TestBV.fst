module TestBV

open FStar.UInt
open FStar.Tactics
open FStar.Tactics.BV

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

module U64 = FStar.UInt64
let test5 (x y: U64.t) =
    assert_by_tactic (logand #64 (U64.v x) (U64.v y) == logand #64 (U64.v y) (U64.v x))
                     (bv_tac ())

let unfold_logand64 (x y: U64.t) : Lemma 
  (U64.v (U64.logand x y) == logand #64 (U64.v x) (U64.v y))
  = ()


let v64_eq (x y: U64.t) : Lemma 
  (requires (U64.v x == U64.v y))
  (ensures (x == y))
  = ()

let trans (a:Type) 
          (w x y z : a)
	  (_:squash (w == x))
          (_:squash (z == y))
          (_:squash (x == y))
        : Lemma (w == z)
        = ()

let bv_tac ()  =
  apply_lemma (quote eq_to_bv);;
  apply_lemma (quote FStar.Tactics.BV.trans);;
  arith_to_bv_tac;;
  arith_to_bv_tac;;
  set_options "--smtencoding.elim_box true";;
  dump "BEFORE SMT!" ;;
  smt

let test6 (x y: U64.t) =
    assert_by_tactic (U64.logand x y == U64.logand y x)
                     (apply_lemma (quote v64_eq) ;;
                      dump "A" ;;
                      apply_lemma (quote trans) ;; 
                      apply_lemma (quote unfold_logand64) ;;
                      dump "B";;
                      apply_lemma (quote unfold_logand64) ;;
                      dump "C";;
                      norm [] ;;
                      bv_tac ())
                     
// //cannot prove
// (* let test5 (x : uint_t 32) = *)
// (*     assert_by_tactic (shift_left #32 x 3 == shift_left #32 (shift_left #32 x 2) 1) *)
// (*                      (prune "";; addns "Prims";; bv_tac ()) *)
