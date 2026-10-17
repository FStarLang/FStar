module BvBinaryOps

module BV = FStar.BV


module UInt = FStar.UInt
module Int = FStar.Int


(** Tests for bvshl *)

// small integer works ok with bvshl or bvshl'
let lemma_test_bv8 (bv: BV.bv_t 8) (i: UInt.uint_t 3): unit =
  let shl = BV.bvshl #8 (BV.int2bv #8 1) i in
  assert ((BV.bvand #8 (BV.bvor #8 bv shl) shl <> BV.int2bv #8 0 == true))

let lemma_test_bv8' (bv: BV.bv_t 8) (i: UInt.uint_t 3): unit =
  let unfold i' = BV.bv_uext #3 #5 (BV.int2bv #3 i) in
  let unfold shl = (BV.bvshl' #8 (BV.int2bv #8 1) i') in
  assert ((BV.bvand #8 (BV.bvor #8 bv shl) shl <> BV.int2bv #8 0 == true))

// The corresponding 64-bit version doesn't usually prove with bvshl.
// The uint is converted directly to a 64-bit bv and Z3 doesn't seem to take
// into account the range of the nat in this conversion.

// let lemma_test_bv64 (bv: BV.bv_t 64) (i: UInt.uint_t 6): unit =
//   let shl = BV.bvshl #64 (BV.int2bv #64 1) i in
//   assert ((BV.bvand #64 (BV.bvor #64 bv shl) shl <> BV.int2bv #64 0 == true))

// But if we convert the uint to a 6-bit bv first and then zero-extend it, it's
// much clearer that the top 58 bits are zeros:

let lemma_test_bv64' (bv: BV.bv_t 64) (i: UInt.uint_t 6): unit =
  let unfold i' = BV.bv_uext #6 #58 (BV.int2bv #6 i) in
  let unfold shl = BV.bvshl' #64 (BV.int2bv #64 1) i' in
  assert ((BV.bvand #64 (BV.bvor #64 bv shl) shl <> BV.int2bv #64 0 == true))

(** Tests for division and mod *)

// This follows from lemma bvdiv_unsafe_sound, but it doesn't have an SMT pattern,
// so if it succeeds then the encoding is probably correct.
let lemma_test_bvdiv_unsafe (bv: BV.bv_t 64) (num: UInt.uint_t 8 { num <> 0 }): unit =
  assert (BV.bvdiv_unsafe #64 bv (BV.int2bv #64 num) == BV.bvdiv #64 bv num)

let lemma_test_bvmod_unsafe (bv: BV.bv_t 64) (num: UInt.uint_t 8 { num <> 0 }): unit =
  assert (BV.bvmod_unsafe #64 bv (BV.int2bv #64 num) == BV.bvmod #64 bv num)

let lemma_test_bvmul' (bv: BV.bv_t 64) (num: UInt.uint_t 64): unit =
  assert (BV.bvmul' #64 bv (BV.int2bv #64 num) == BV.bvmul #64 bv num)

(** Tests for bvnot *)
let lemma_bvnot_test (bv: BV.bv_t 64) : unit =
  let not1 = BV.bvnot #64 bv in
  let not2 = BV.bvnot #64 (BV.bvnot #64 bv) in
  assert (not2 == bv);
  assert (not1 <> bv)

(** Tests for bv_extract *)

let lemma_bv_extract_constant () : unit =
  assert (BV.bv_extract #8 (BV.int2bv #8 0b10110110) 5 2
          == BV.int2bv #4 0b1101)

let lemma_bv_extract_single_bit () : unit =
  assert (BV.bv_extract #8 (BV.int2bv #8 0b10110110) 4 4
          == BV.int2bv #1 1)

let lemma_bv_extract_full_width (bv: BV.bv_t 8) : unit =
  assert (BV.bv_extract #8 bv 7 0 == bv)

let lemma_bv_extract_composition (bv: BV.bv_t 16) : unit =
  assert (BV.bv_extract #8 (BV.bv_extract #16 bv 11 4) 5 2
          == BV.bv_extract #16 bv 9 6)

(** Native consumers of extracted bit vectors *)

let lemma_bvnot_extract_explicit (v: BV.bv_t 8) : unit =
  assert (BV.bvnot #4 (BV.bv_extract #8 v 5 2)
          == BV.bv_extract #8 (BV.bvnot #8 v) 5 2)

let lemma_bvnot_extract_inferred (v: BV.bv_t 8) : unit =
  assert (BV.bvnot (BV.bv_extract #8 v 5 2)
          == BV.bv_extract #8 (BV.bvnot #8 v) 5 2)

let lemma_bvand_extract_explicit (v w: BV.bv_t 8) : unit =
  assert (BV.bvand #4 (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 w 5 2)
          == BV.bv_extract #8 (BV.bvand #8 v w) 5 2)

let lemma_bvand_extract_inferred (v w: BV.bv_t 8) : unit =
  assert (BV.bvand (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 w 5 2)
          == BV.bv_extract #8 (BV.bvand #8 v w) 5 2)

let lemma_bvor_extract_explicit (v w: BV.bv_t 8) : unit =
  assert (BV.bvor #4 (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 w 5 2)
          == BV.bv_extract #8 (BV.bvor #8 v w) 5 2)

let lemma_bvor_extract_inferred (v w: BV.bv_t 8) : unit =
  assert (BV.bvor (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 w 5 2)
          == BV.bv_extract #8 (BV.bvor #8 v w) 5 2)

let lemma_bvxor_extract_explicit (v w: BV.bv_t 8) : unit =
  assert (BV.bvxor #4 (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 w 5 2)
          == BV.bv_extract #8 (BV.bvxor #8 v w) 5 2)

let lemma_bvxor_extract_inferred (v w: BV.bv_t 8) : unit =
  assert (BV.bvxor (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 w 5 2)
          == BV.bv_extract #8 (BV.bvxor #8 v w) 5 2)

let lemma_bvadd_extract_explicit (v w: BV.bv_t 8) : unit =
  assert (BV.bvadd #4 (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 w 5 2)
          == BV.bvadd #4 (BV.bv_extract #8 w 5 2) (BV.bv_extract #8 v 5 2))

let lemma_bvadd_extract_inferred (v w: BV.bv_t 8) : unit =
  assert (BV.bvadd (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 w 5 2)
          == BV.bvadd (BV.bv_extract #8 w 5 2) (BV.bv_extract #8 v 5 2))

let lemma_bv_uext_extract_explicit (v: BV.bv_t 8) : unit =
  assert (BV.bv_uext #4 #4 (BV.bv_extract #8 v 5 2)
          == BV.bv_concat #4 #4 (BV.int2bv #4 0) (BV.bv_extract #8 v 5 2))

let lemma_bv_uext_extract_inferred (v: BV.bv_t 8) : unit =
  assert (BV.bv_uext #_ #4 (BV.bv_extract #8 v 5 2)
          == BV.bv_concat #4 #4 (BV.int2bv #4 0) (BV.bv_extract #8 v 5 2))

let lemma_bvult_extract_explicit (v: BV.bv_t 8) : unit =
  assert (BV.bvult #4 (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 v 5 2) == false)

let lemma_bvult_extract_inferred (v: BV.bv_t 8) : unit =
  assert (BV.bvult (BV.bv_extract #8 v 5 2) (BV.bv_extract #8 v 5 2) == false)

let lemma_bv2int_extract_explicit (v: BV.bv_t 8) : unit =
  assert (BV.bv2int #4 (BV.bv_extract #8 v 5 2)
          == (BV.bv2int #8 v / 4) % 16)

let lemma_bv2int_extract_inferred (v: BV.bv_t 8) : unit =
  assert (BV.bv2int (BV.bv_extract #8 v 5 2)
          == (BV.bv2int #8 v / 4) % 16)

(** Tests for bvrol / bvror *)

// rotate left by 0 is identity
let lemma_test_bvrol_zero (bv: BV.bv_t 8) : unit =
  assert (BV.bvrol #8 bv 0 == bv)

// rotate right by 0 is identity
let lemma_test_bvror_zero (bv: BV.bv_t 8) : unit =
  assert (BV.bvror #8 bv 0 == bv)

// rotate left then right by same amount is identity
let lemma_test_bvrol_bvror_inverse_8 (bv: BV.bv_t 8) (i: UInt.uint_t 3) : unit =
  assert (BV.bvror #8 (BV.bvrol #8 bv i) i == bv)

// rotate right then left by same amount is identity
let lemma_test_bvror_bvrol_inverse_8 (bv: BV.bv_t 8) (i: UInt.uint_t 3) : unit =
  assert (BV.bvrol #8 (BV.bvror #8 bv i) i == bv)

// rotating by full width is identity
let lemma_test_bvrol_full_8 (bv: BV.bv_t 8) : unit =
  assert (BV.bvrol #8 bv 8 == bv)

let lemma_test_bvror_full_8 (bv: BV.bv_t 8) : unit =
  assert (BV.bvror #8 bv 8 == bv)

// rotating a known constant: 0x0F rotated left by 4 = 0xF0
let lemma_test_bvrol_constant () : unit =
  assert (BV.bvrol #8 (BV.int2bv #8 0x0F) 4 == BV.int2bv #8 0xF0)

// rotating a known constant back: 0xF0 rotated right by 4 = 0x0F
let lemma_test_bvror_constant () : unit =
  assert (BV.bvror #8 (BV.int2bv #8 0xF0) 4 == BV.int2bv #8 0x0F)

// primed variants (bv_t arg for rotation amount)
let lemma_test_bvrol'_8 (bv: BV.bv_t 8) (i: UInt.uint_t 3) : unit =
  let unfold i' = BV.bv_uext #3 #5 (BV.int2bv #3 i) in
  assert (BV.bvror' #8 (BV.bvrol' #8 bv i') i' == bv)

let lemma_test_bvror'_8 (bv: BV.bv_t 8) (i: UInt.uint_t 3) : unit =
  let unfold i' = BV.bv_uext #3 #5 (BV.int2bv #3 i) in
  assert (BV.bvrol' #8 (BV.bvror' #8 bv i') i' == bv)

(** Remaining SMT-LIB bitvector primitives *)

let lemma_bv_concat () : unit =
  assert (BV.bv_concat #4 #4 (BV.int2bv #4 0xa) (BV.int2bv #4 0x3)
          == BV.int2bv #8 0xa3)

let lemma_bv_repeat () : unit =
  assert (BV.bv_repeat #4 #2 (BV.int2bv #4 0xa) == BV.int2bv #8 0xaa)

let lemma_bv_sext () : unit =
  assert (BV.bv_sext #4 #4 (BV.int2bv #4 0xa) == BV.int2bv #8 0xfa)

let lemma_symbolic_indexed_ops (#i: pos) (a b: BV.bv_t 4)
  : Lemma
      (requires a == b)
      (ensures (BV.bv_uext #4 #i a == BV.bv_uext #4 #i b
             /\ BV.bv_sext #4 #i a == BV.bv_sext #4 #i b
             /\ BV.bv_repeat #4 #i a == BV.bv_repeat #4 #i b))
  = ()

let lemma_bvneg () : unit =
  assert (BV.bvneg #4 (BV.int2bv #4 3) == BV.int2bv #4 13)

let lemma_bvnand () : unit =
  assert (BV.bvnand #4 (BV.int2bv #4 12) (BV.int2bv #4 10)
          == BV.int2bv #4 7)

let lemma_bvnor () : unit =
  assert (BV.bvnor #4 (BV.int2bv #4 12) (BV.int2bv #4 10)
          == BV.int2bv #4 1)

let lemma_bvxnor () : unit =
  assert (BV.bvxnor #4 (BV.int2bv #4 12) (BV.int2bv #4 10)
          == BV.int2bv #4 9)

let lemma_bvcomp () : unit =
  assert (BV.bvcomp #4 (BV.int2bv #4 5) (BV.int2bv #4 5) == BV.int2bv #1 1);
  assert (BV.bvcomp #4 (BV.int2bv #4 5) (BV.int2bv #4 6) == BV.int2bv #1 0)

let lemma_unsigned_comparisons () : unit =
  assert (BV.bvule #4 (BV.int2bv #4 5) (BV.int2bv #4 5));
  assert (BV.bvugt #4 (BV.int2bv #4 9) (BV.int2bv #4 5));
  assert (BV.bvuge #4 (BV.int2bv #4 9) (BV.int2bv #4 9))

let lemma_signed_comparisons () : unit =
  let minus_two = BV.int2bv #4 (Int.to_uint #4 (-2)) in
  let three = BV.int2bv #4 (Int.to_uint #4 3) in
  assert (BV.bvslt #4 minus_two three);
  assert (BV.bvsle #4 minus_two minus_two);
  assert (BV.bvsgt #4 three minus_two);
  assert (BV.bvsge #4 three three)

let lemma_signed_arithmetic () : unit =
  let minus_seven = BV.int2bv #4 (Int.to_uint #4 (-7)) in
  let three = BV.int2bv #4 (Int.to_uint #4 3) in
  assert (BV.bvsdiv #4 minus_seven three == BV.int2bv #4 (Int.to_uint #4 (-2)));
  assert (BV.bvsrem #4 minus_seven three == BV.int2bv #4 (Int.to_uint #4 (-1)));
  assert (BV.bvsmod #4 minus_seven three == BV.int2bv #4 (Int.to_uint #4 2));
  assert (BV.bvashr #4 (BV.int2bv #4 (Int.to_uint #4 (-8))) (BV.int2bv #4 2)
          == BV.int2bv #4 (Int.to_uint #4 (-2)))

let lemma_signed_arithmetic_edge_cases () : unit =
  let min = BV.int2bv #4 (Int.to_uint #4 (-8)) in
  let minus_one = BV.int2bv #4 (Int.to_uint #4 (-1)) in
  let zero = BV.int2bv #4 (Int.to_uint #4 0) in
  assert (BV.bvsdiv #4 (BV.int2bv #4 (Int.to_uint #4 7)) zero == minus_one);
  assert (BV.bvsdiv #4 (BV.int2bv #4 (Int.to_uint #4 (-7))) zero
          == BV.int2bv #4 (Int.to_uint #4 1));
  assert (BV.bvsrem #4 min zero == min);
  assert (BV.bvsmod #4 min zero == min);
  assert (BV.bvsdiv #4 min minus_one == min);
  assert (BV.bvsrem #4 min minus_one == zero);
  assert (BV.bvsmod #4 min minus_one == zero);
  assert (BV.bvashr #4 min (BV.int2bv #4 7) == minus_one);
  assert (BV.bvashr #4 (BV.int2bv #4 (Int.to_uint #4 7)) (BV.int2bv #4 7) == zero)

let lemma_signed_arithmetic_8bit_edges () : unit =
  let min = BV.int2bv #8 (Int.to_uint #8 (-128)) in
  let minus_one = BV.int2bv #8 (Int.to_uint #8 (-1)) in
  let zero = BV.int2bv #8 (Int.to_uint #8 0) in
  assert (BV.bvsdiv #8 min minus_one == min);
  assert (BV.bvsrem #8 min minus_one == zero);
  assert (BV.bvsmod #8 min minus_one == zero);
  assert (BV.bvashr #8 min (BV.int2bv #8 9) == minus_one);
  assert (BV.bvsaddo #8 (BV.int2bv #8 (Int.to_uint #8 127))
                         (BV.int2bv #8 (Int.to_uint #8 1)));
  assert (BV.bvssubo #8 min (BV.int2bv #8 (Int.to_uint #8 1)))

let lemma_signed_symbolic_8 (a: BV.bv_t 8) : unit =
  let one = BV.int2bv #8 1 in
  let zero = BV.int2bv #8 0 in
  assert (BV.bvsle #8 a a);
  assert (not (BV.bvslt #8 a a));
  assert (BV.bvsdiv #8 a one == a);
  assert (BV.bvsrem #8 a one == zero);
  assert (BV.bvsmod #8 a one == zero)

let lemma_bvsmod_sign_cases_8 () : unit =
  let bv (x: Int.int_t 8) = BV.int2bv #8 (Int.to_uint #8 x) in
  assert (BV.bvsmod #8 (bv 13) (bv 5) == bv 3);
  assert (BV.bvsmod #8 (bv 13) (bv (-5)) == bv (-2));
  assert (BV.bvsmod #8 (bv (-13)) (bv 5) == bv 2);
  assert (BV.bvsmod #8 (bv (-13)) (bv (-5)) == bv (-3));
  assert (BV.bvsmod #8 (bv 10) (bv (-5)) == bv 0)

let lemma_symbolic_bitwise (a b: BV.bv_t 8) : unit =
  assert (BV.bvnand #8 a b == BV.bvnot #8 (BV.bvand #8 a b));
  assert (BV.bvnor #8 a b == BV.bvnot #8 (BV.bvor #8 a b));
  assert (BV.bvxnor #8 a b == BV.bvnot #8 (BV.bvxor #8 a b));
  assert (BV.bvcomp #8 a b == (if a = b then BV.int2bv #1 1 else BV.int2bv #1 0))

let lemma_overflow_predicates () : unit =
  assert (BV.bvnego #4 (BV.int2bv #4 (Int.to_uint #4 (-8))));
  assert (BV.bvuaddo #4 (BV.int2bv #4 15) (BV.int2bv #4 1));
  assert (BV.bvsaddo #4 (BV.int2bv #4 (Int.to_uint #4 7))
                         (BV.int2bv #4 (Int.to_uint #4 1)));
  assert (BV.bvumulo #4 (BV.int2bv #4 8) (BV.int2bv #4 2));
  assert (BV.bvsmulo #4 (BV.int2bv #4 (Int.to_uint #4 4))
                         (BV.int2bv #4 (Int.to_uint #4 2)));
  assert (BV.bvusubo #4 (BV.int2bv #4 0) (BV.int2bv #4 1));
  assert (BV.bvssubo #4 (BV.int2bv #4 (Int.to_uint #4 (-8)))
                         (BV.int2bv #4 (Int.to_uint #4 1)));
  assert (BV.bvsdivo #4 (BV.int2bv #4 (Int.to_uint #4 (-8)))
                         (BV.int2bv #4 (Int.to_uint #4 (-1))))

let lemma_integer_conversions () : unit =
  assert (BV.sbv_to_int #4 (BV.int2bv #4 14) == -2)