module TestBV

open FStar.UInt
open FStar.Tactics
open FStar.Tactics.BV

let test1 (x y: uint_t 64) =
    assert_by_tactic (logand x y == logand y x)
                     (bv_tac ())

let test2 (x y : uint_t 64) = 
    assert_by_tactic (logand (logand x y) y == logand y (logand y x))
                     (bv_tac ())

let test3 (x y : uint_t 64) = 
    assert_by_tactic (logand (logand (logand x y) x) y == logand y (logand x (logand y x)))
                     (bv_tac ())

let test4 (x y : uint_t 64) = 
    assert_by_tactic (logand (logand x (logxor x y)) y == logand y (logand x (logxor y x)))
                     (bv_tac ())

module U64 = FStar.UInt64
let test5 (x y: U64.t) =
    assert_by_tactic (logand (U64.v x) (U64.v y) == logand (U64.v y) (U64.v x))
                     (bv_tac ())

let unfold_logand64 (x y: U64.t) : Lemma 
  (U64.v (U64.logand x y) == logand #64 (U64.v x) (U64.v y))
  = ()

let unfold_logor64 (x y: U64.t) : Lemma 
  (U64.v (U64.logor x y) == logor #64 (U64.v x) (U64.v y))
  = ()

let unfold_logxor64 (x y: U64.t) : Lemma 
  (U64.v (U64.logxor x y) == logxor #64 (U64.v x) (U64.v y))
  = ()

let unfold64 () = 
  or_else (apply_lemma (quote unfold_logand64))
          (or_else (apply_lemma (quote unfold_logor64))
                   (or_else (apply_lemma (quote unfold_logxor64))
                           idtac))

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

// let bv64_tac ()  =
//   apply_lemma (quote eq_to_bv);;
//   apply_lemma (quote FStar.Tactics.BV.trans);;
//   arith_to_bv_tac;;
//   arith_to_bv_tac;;
//   set_options "--smtencoding.elim_box true";;
//   norm [delta];;
//   fail #unit "BEFORE SMT!" ;;
//   smt

//#reset-options "--log_queries --z3refresh"
let test6 (x y: U64.t) =
    assert_by_tactic (U64.logand x y == U64.logand y x)
                     (apply_lemma (quote v64_eq) ;;
                      apply_lemma (quote trans) ;; 
                      unfold64 () ;; unfold64() ;;
                      norm [] ;;
                      bv_tac ())

