module ExtUInt128

/// FStar.UInt128: the widest machine integer, and the one with the least
/// shared implementation between the backends.
///
///   - OCaml gets whatever `FStar.UInt128.fst` extracts to, i.e. a *pair of
///     64-bit words* with the arithmetic written out in F*.
///   - C is expected to use a native `unsigned __int128` when the compiler has
///     one (karamel/include/krml/internal/../../../krmllib/dist/generic/
///     fstar_uint128_gcc64.h) and fall back to the struct implementation
///     otherwise, so the very same F* program is compiled two completely
///     different ways depending on the host.
///   - Rust has no `u128` mapping in Karamel at all.
///
/// That makes it a prime spot for the two halves of a 128-bit value to be
/// swapped, truncated or sign-extended by one backend and not the others.
///
/// There is no literal syntax for a 128-bit constant, so the operands are
/// built with `uint64_to_uint128` from top-level 64-bit literals. That keeps
/// them opaque to the constant folder (see README.md) without producing a
/// computed top-level binding, which the Rust backend rejects.

module U32  = FStar.UInt32
module U64  = FStar.UInt64
module U128 = FStar.UInt128
module I32  = FStar.Int32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let u64_max : U64.t = 18446744073709551615uL
let five    : U64.t = 5uL
let seven   : U64.t = 7uL
let one64   : U64.t = 1uL
let zero64  : U64.t = 0uL
let big     : U64.t = 12297829382473034410uL

/// Addition and subtraction have to carry between the two 64-bit halves.
/// `u64_max + 1` is the smallest value that does not fit in 64 bits, so a
/// backend that keeps only the low word gets 0 here.
#push-options "--z3rlimit 60"
let carry_tests () : I32.t =
  let m = U128.uint64_to_uint128 u64_max in
  let one = U128.uint64_to_uint128 one64 in
  let sum = U128.add m one in
     chk 1l (U128.gt sum m)
 &&& chk 2l (U128.eq (U128.sub sum one) m)
     (* the low 64 bits of 2^64 are zero, and the value is *not* zero *)
 &&& chk 3l (U64.eq (U128.uint128_to_uint64 sum) zero64)
 &&& chk 4l (not (U128.eq sum (U128.uint64_to_uint128 zero64)))
#pop-options

/// `mul_wide` is the reason UInt128 exists: the full 128-bit product of two
/// 64-bit words. If a backend computes it at 64 bits the high half is lost.
#push-options "--z3rlimit 120"
let mul_wide_tests () : I32.t =
  let p = U128.mul_wide u64_max u64_max in
  let small = U128.mul_wide five seven in
     (* (2^64-1)^2 = 2^128 - 2^65 + 1, which does not fit in 64 bits *)
     chk 10l (U128.gt p (U128.uint64_to_uint128 u64_max))
     (* its low 64 bits are 1 *)
 &&& chk 11l (U64.eq (U128.uint128_to_uint64 p) one64)
     (* a product that does fit must agree with the 64-bit one *)
 &&& chk 12l (U128.eq small (U128.uint64_to_uint128 (U64.mul five seven)))
 &&& chk 13l (U64.eq (U128.uint128_to_uint64 small) (U64.mul five seven))
#pop-options

/// Round-tripping through the 64-bit type truncates, and comparisons must look
/// at both halves rather than just the low one.
#push-options "--z3rlimit 60"
let cast_cmp_tests () : I32.t =
  let a = U128.uint64_to_uint128 big in
  let hi = U128.shift_left (U128.uint64_to_uint128 one64) 64ul in
     chk 20l (U64.eq (U128.uint128_to_uint64 a) big)
 &&& chk 21l (U128.lt a hi)
 &&& chk 22l (U128.gt hi (U128.uint64_to_uint128 u64_max))
     (* 2^64 truncates to 0, so a backend comparing only low words says equal *)
 &&& chk 23l (U64.eq (U128.uint128_to_uint64 hi) zero64)
 &&& chk 24l (not (U128.eq hi (U128.uint64_to_uint128 zero64)))
 &&& chk 25l (U128.gte a a)
 &&& chk 26l (U128.lte a a)
#pop-options

/// Shifts have to move bits across the 64-bit boundary in both directions.
#push-options "--z3rlimit 120"
let shift_tests () : I32.t =
  let one = U128.uint64_to_uint128 one64 in
  let hi = U128.shift_left one 64ul in
     chk 30l (U128.eq (U128.shift_right hi 64ul) one)
 &&& chk 31l (U128.eq (U128.shift_left one 0ul) one)
 &&& chk 32l (U128.eq (U128.shift_right one 0ul) one)
     (* shifting the low word up and back down is the identity *)
 &&& chk 33l (U128.eq (U128.shift_right (U128.shift_left one 127ul) 127ul) one)
     (* ... and shifting it off the top gives zero *)
 &&& chk 34l (U128.eq (U128.shift_right hi 127ul) (U128.uint64_to_uint128 zero64))
#pop-options

/// Bitwise operations, via the identities F* can actually prove at this width
/// (see FINDINGS.md #13): x&x = x, x|0 = x, x^x = 0, ~~x = x.
#push-options "--z3rlimit 120"
let logic_tests () : I32.t =
  let a = U128.uint64_to_uint128 big in
  let z = U128.uint64_to_uint128 zero64 in
  FStar.UInt.logand_self #128 (U128.v a);
  FStar.UInt.logor_lemma_1 #128 (U128.v a);
  FStar.UInt.logxor_self #128 (U128.v a);
  FStar.UInt.lognot_self #128 (U128.v a);
     chk 40l (U128.eq (U128.logand a a) a)
 &&& chk 41l (U128.eq (U128.logor a z) a)
 &&& chk 42l (U128.eq (U128.logxor a a) z)
 &&& chk 43l (U128.eq (U128.lognot (U128.lognot a)) a)
#pop-options

let main () : I32.t =
     carry_tests ()
 &&& mul_wide_tests ()
 &&& cast_cmp_tests ()
 &&& shift_tests ()
 &&& logic_tests ()
