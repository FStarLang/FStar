module BvBinaryOps

module BV = FStar.BV


module UInt = FStar.UInt

#set-options "--split_queries always"

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