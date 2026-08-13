module ExtInt128

/// FStar.Int128: the signed counterpart of FStar.UInt128, and the much less
/// travelled of the two. Unlike UInt128 it has `mul`, `div` and `rem`, so it
/// exercises signed 128-bit division -- including the rounding direction on
/// negative operands, which differs between C (truncation toward zero),
/// OCaml's Zarith-free two-word implementation, and anything Karamel might
/// emit.
///
/// Karamel's krmllib ships `FStar_UInt128.h`, `FStar_UInt128_Verified.h`,
/// `fstar_uint128_gcc64.h` and `fstar_uint128_msvc.h`, but *nothing at all*
/// for Int128; see FINDINGS.md.
///
/// There is no `int64_to_int128`, so operands are widened with `mul_wide x 1L`,
/// whose postcondition gives exactly `v (mul_wide x 1L) == Int64.v x`. That is
/// opaque to the constant folder while still being provably a widening.

module I64  = FStar.Int64
module I128 = FStar.Int128
module I32  = FStar.Int32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let widen (x:I64.t) : y:I128.t{I128.v y == I64.v x} = I128.mul_wide x 1L

let p7  : I64.t = 7L
let m7  : I64.t = -7L
let p3  : I64.t = 3L
let m3  : I64.t = -3L
let p21 : I64.t = 21L
let m21 : I64.t = -21L
let m8  : I64.t = -8L
let i64_min : I64.t = -9223372036854775808L

/// Sign has to survive the widening: a backend that widens through an unsigned
/// type turns -7 into 2^128 - 7, which is positive.
let sign_tests () : I32.t =
     chk 1l (I128.gt (widen p7) I128.zero)
 &&& chk 2l (I128.lt (widen m7) I128.zero)
 &&& chk 3l (I128.lt (widen m7) (widen p7))
 &&& chk 4l (I128.eq (widen p7) (widen p7))
 &&& chk 5l (I128.lt (widen i64_min) I128.zero)
 &&& chk 6l (I128.gte (widen p7) (widen p7))
 &&& chk 7l (I128.lte (widen m7) (widen p7))

let arith_tests () : I32.t =
     chk 10l (I128.eq (I128.add (widen p7) (widen m7)) I128.zero)
 &&& chk 11l (I128.eq (I128.sub I128.zero (widen p7)) (widen m7))
 &&& chk 12l (I128.eq (I128.mul (widen p7) (widen p3)) (widen p21))
 &&& chk 13l (I128.eq (I128.mul (widen m7) (widen p3)) (widen m21))
 &&& chk 14l (I128.eq (I128.mul (widen m7) (widen m3)) (widen p21))
 &&& chk 15l (I128.eq (I128.add (widen p7) I128.one) (widen 8L))

/// `mul_wide` of two 64-bit values must not be computed at 64 bits.
/// (-2^63)^2 = 2^126, which is positive and far wider than 64 bits.
#push-options "--z3rlimit 60"
let mul_wide_tests () : I32.t =
  let sq = I128.mul_wide i64_min i64_min in
     chk 20l (I128.gt sq I128.zero)
 &&& chk 21l (I128.gt sq (widen 9223372036854775807L))
     (* the product does not collapse to zero, which is what truncating to
        64 bits would give, since (-2^63)^2 mod 2^64 = 0 *)
 &&& chk 22l (not (I128.eq sq I128.zero))
#pop-options

/// Signed division and remainder on negative operands. The Euclidean vs.
/// truncating question is settled here by the division identity
/// `(a/b)*b + a%b = a`, which every backend has to satisfy, plus exact values.
#push-options "--z3rlimit 120"
let div_tests () : I32.t =
  let a = widen m7 in let b = widen p3 in
  let c = widen p7 in let d = widen m3 in
     chk 30l (I128.eq (I128.add (I128.mul (I128.div a b) b) (I128.rem a b)) a)
 &&& chk 31l (I128.eq (I128.add (I128.mul (I128.div c d) d) (I128.rem c d)) c)
 &&& chk 32l (I128.eq (I128.div (widen p21) (widen p3)) (widen p7))
 &&& chk 33l (I128.eq (I128.div (widen m21) (widen p3)) (widen m7))
 &&& chk 34l (I128.eq (I128.rem (widen p21) (widen p3)) I128.zero)
 &&& chk 35l (I128.eq (I128.div (widen p7) I128.one) (widen p7))
#pop-options

/// `FStar.Int` has `logand_self` and `logxor_self` but no `logor_self` and no
/// `lognot_self`, so those two go through the signed/unsigned bridge: the
/// signed bitwise operations are *definitionally* the unsigned ones applied to
/// the two's-complement representation, which unlocks the `FStar.UInt` lemma
/// library. See ExtIntSigned.fst for the same recipe at smaller widths.
let logor_bridge (#n:pos) (a b : FStar.Int.int_t n)
  : Lemma (FStar.Int.logor a b ==
           FStar.Int.from_uint (FStar.UInt.logor (FStar.Int.to_uint a) (FStar.Int.to_uint b)))
  = ()

let lognot_bridge (#n:pos) (a : FStar.Int.int_t n)
  : Lemma (FStar.Int.lognot a ==
           FStar.Int.from_uint (FStar.UInt.lognot (FStar.Int.to_uint a)))
  = ()

let from_to_uint (#n:pos) (a : FStar.Int.int_t n)
  : Lemma (FStar.Int.from_uint (FStar.Int.to_uint a) == a) = ()

let to_from_uint (#n:pos) (u : FStar.UInt.uint_t n)
  : Lemma (FStar.Int.to_uint (FStar.Int.from_uint #n u) == u) = ()

/// Bitwise identities; see FINDINGS.md #13 for why these are stated
/// relationally rather than against literal results.
#push-options "--z3rlimit 120"
let logic_tests () : I32.t =
  let a = widen m7 in

  FStar.Int.logand_self #128 (I128.v a);
  FStar.Int.logxor_self #128 (I128.v a);
  logor_bridge #128 (I128.v a) 0;
  FStar.UInt.logor_lemma_1 #128 (FStar.Int.to_uint (I128.v a));
  from_to_uint #128 (I128.v a);
  lognot_bridge #128 (I128.v a);
  to_from_uint #128 (FStar.UInt.lognot (FStar.Int.to_uint (I128.v a)));
  lognot_bridge #128 (FStar.Int.lognot (I128.v a));
  FStar.UInt.lognot_self #128 (FStar.Int.to_uint (I128.v a));
     chk 40l (I128.eq (I128.logand a a) a)
 &&& chk 41l (I128.eq (I128.logxor a a) I128.zero)
 &&& chk 42l (I128.eq (I128.logor a I128.zero) a)
 &&& chk 43l (I128.eq (I128.lognot (I128.lognot a)) a)
#pop-options

/// An arithmetic right shift of a negative number stays negative: the sign bit
/// must be replicated, not filled with zeroes. Only the sign bit is checked
/// because pinning the exact 128-bit result is not feasible (FINDINGS.md #13).
#push-options "--z3rlimit 120"
let shift_tests () : I32.t =
  let a = widen m8 in
  FStar.Int.shift_arithmetic_right_lemma_1 #128 (I128.v a) 1 0;
  FStar.Int.sign_bit_negative #128 (I128.v (I128.shift_arithmetic_right a 1ul));
     chk 50l (I128.lt (I128.shift_arithmetic_right a 1ul) I128.zero)
 &&& chk 51l (I128.eq (I128.shift_arithmetic_right a 0ul) a)
 &&& chk 52l (I128.eq (I128.shift_left I128.one 0ul) I128.one)
#pop-options

let main () : I32.t =
     sign_tests ()
 &&& arith_tests ()
 &&& mul_wide_tests ()
 &&& div_tests ()
 &&& logic_tests ()
 &&& shift_tests ()
