module ExtUIntMask

/// The constant-time comparison primitives `eq_mask` and `gte_mask`, plus the
/// unary negation `minus`. These are completely untested by the existing
/// extraction suite despite being the primitives HACL* leans on hardest.
///
/// Three things make them worth their own module:
///
///  1. They are specified by their *result*, not by their implementation:
///     `eq_mask a b` is `2^n - 1` when `a = b` and `0` otherwise. A backend is
///     free to implement them however it likes, so nothing but a runtime check
///     ties the implementations together.
///  2. They carry `[@ CNoInline ]`, so this is also a test that the attribute
///     does not break extraction.
///  3. `gte_mask` must be an *unsigned* comparison. Implemented with a signed
///     one, `gte_mask 0xFFFFFFFF 1` yields 0 instead of all-ones -- a silent
///     wrong value in exactly the code that is supposed to be constant time.
///
/// `minus` is `add_mod (lognot a) 1`, i.e. two's complement negation, and has
/// no `Pure` postcondition, so its value can only be pinned where F* can
/// evaluate `lognot` -- 8 bits (FINDINGS.md #13).

module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32
module U   = FStar.UInt

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let u8_max  : U8.t  = 255uy
let u16_max : U16.t = 65535us
let u32_max : U32.t = 4294967295ul
let u64_max : U64.t = 18446744073709551615uL

let c7    : U32.t = 7ul
let c7'   : U32.t = 7ul
let c9    : U32.t = 9ul
let c0_32 : U32.t = 0ul
let c1_32 : U32.t = 1ul

let c7_8   : U8.t  = 7uy
let c7_8'  : U8.t  = 7uy
let c9_8   : U8.t  = 9uy
let c7_16  : U16.t = 7us
let c7_16' : U16.t = 7us
let c9_16  : U16.t = 9us
let c7_64  : U64.t = 7uL
let c7_64' : U64.t = 7uL
let c9_64  : U64.t = 9uL
let c1_64  : U64.t = 1uL
let c1_8   : U8.t  = 1uy
let c1_16  : U16.t = 1us

/// The all-ones results are stated as literals, so `pow2 n - 1` has to be
/// evaluated; the SMT solver will not do that on its own at 64 bits.
let ones_norm () : Lemma (pow2 8 - 1 == 255 /\ pow2 16 - 1 == 65535 /\
                          pow2 32 - 1 == 4294967295 /\
                          pow2 64 - 1 == 18446744073709551615) =
  assert_norm (pow2 8 - 1 == 255);
  assert_norm (pow2 16 - 1 == 65535);
  assert_norm (pow2 32 - 1 == 4294967295);
  assert_norm (pow2 64 - 1 == 18446744073709551615)

/// Equal operands give all-ones, unequal operands give zero, at every width.
/// Split per width because the accumulated path condition of a long `&&&`
/// chain is enough on its own to time the solver out.
#push-options "--z3rlimit 60"
let eq_mask_32 () : I32.t =
  ones_norm ();
     chk 1l (U32.eq (U32.eq_mask c7 c7') u32_max)
 &&& chk 2l (U32.eq (U32.eq_mask c7 c9) 0ul)
     (* the all-ones operand is the one a narrowing bug would mangle *)
 &&& chk 9l (U32.eq (U32.eq_mask u32_max c7) 0ul)

let eq_mask_8 () : I32.t =
  ones_norm ();
     chk 3l (U8.eq (U8.eq_mask c7_8 c7_8') u8_max)
 &&& chk 4l (U8.eq (U8.eq_mask c7_8 c9_8)  0uy)

let eq_mask_16 () : I32.t =
  ones_norm ();
     chk 5l (U16.eq (U16.eq_mask c7_16 c7_16') u16_max)
 &&& chk 6l (U16.eq (U16.eq_mask c7_16 c9_16)  0us)

let eq_mask_64 () : I32.t =
  ones_norm ();
     chk 7l (U64.eq (U64.eq_mask c7_64 c7_64') u64_max)
 &&& chk 8l (U64.eq (U64.eq_mask c7_64 c9_64)  0uL)
 &&& chk 10l (U64.eq (U64.eq_mask u64_max c7_64) 0uL)
#pop-options

/// `gte_mask` has to be unsigned. Checks 24-27 are the ones a signed
/// comparison gets wrong: 0xFF..FF is the *largest* unsigned value, but as a
/// signed value it is -1 and would compare below 1.
#push-options "--z3rlimit 60"
let gte_mask_32 () : I32.t =
  ones_norm ();
     chk 20l (U32.eq (U32.gte_mask c9 c7) u32_max)
 &&& chk 21l (U32.eq (U32.gte_mask c7 c7') u32_max)
 &&& chk 22l (U32.eq (U32.gte_mask c7 c9) 0ul)
 &&& chk 23l (U32.eq (U32.gte_mask c0_32 c1_32) 0ul)
 &&& chk 24l (U32.eq (U32.gte_mask u32_max c1_32) u32_max)
 &&& chk 25l (U32.eq (U32.gte_mask c1_32 u32_max) 0ul)

let gte_mask_64 () : I32.t =
  ones_norm ();
     chk 26l (U64.eq (U64.gte_mask u64_max c1_64) u64_max)
 &&& chk 27l (U64.eq (U64.gte_mask c1_64 u64_max) 0uL)
 &&& chk 34l (U64.eq (U64.gte_mask c9_64 c7_64) u64_max)

let gte_mask_8_16 () : I32.t =
  ones_norm ();
     chk 28l (U8.eq  (U8.gte_mask  u8_max  c1_8)  u8_max)
 &&& chk 29l (U8.eq  (U8.gte_mask  c1_8  u8_max)  0uy)
 &&& chk 30l (U16.eq (U16.gte_mask u16_max c1_16) u16_max)
 &&& chk 31l (U16.eq (U16.gte_mask c1_16 u16_max) 0us)
 &&& chk 32l (U8.eq  (U8.gte_mask  c9_8  c7_8)  u8_max)
 &&& chk 33l (U16.eq (U16.gte_mask c7_16 c9_16) 0us)
#pop-options

/// The masks are meant to be *used* as masks: `x & eq_mask a b` selects `x`
/// or 0 without branching. This checks that the all-ones value really is all
/// ones and not merely non-zero, which is how a `bool`-returning
/// implementation would extract.
#push-options "--z3rlimit 60"
let mask_use_tests () : I32.t =
  U.logand_lemma_2 #32 (U32.v c9);
  U.logand_lemma_1 #32 (U32.v c9);
     chk 40l (U32.eq (U32.logand c9 (U32.eq_mask c7 c7')) c9)
 &&& chk 41l (U32.eq (U32.logand c9 (U32.eq_mask c7 c9)) 0ul)
 &&& chk 42l (U32.eq (U32.logand c9 (U32.gte_mask c9 c7)) c9)
 &&& chk 43l (U32.eq (U32.logand c9 (U32.gte_mask c7 c9)) 0ul)
#pop-options

/// Two's complement negation of an unsigned value. `minus` has no `Pure`
/// postcondition, so it is pinned at 8 bits, where F* can still evaluate
/// `lognot`, and checked relationally elsewhere.
#push-options "--fuel 20 --ifuel 20 --z3rlimit 200"
let minus_tests () : I32.t =
  assert_norm (U.lognot #8 7 == 248);
  assert_norm (U.lognot #8 0 == 255);
  assert_norm (U.lognot #8 1 == 254);
     chk 50l (U8.eq (U8.minus c7_8) 249uy)
 &&& chk 51l (U8.eq (U8.minus c1_8) 255uy)
     (* negating zero gives zero, not 256 *)
 &&& chk 52l (U8.eq (U8.minus 0uy) 0uy)
     (* x + (-x) = 0 modulo 2^8 *)
 &&& chk 53l (U8.eq (U8.add_mod c7_8 (U8.minus c7_8)) 0uy)
 &&& chk 54l (U8.eq (U8.minus (U8.minus c7_8)) c7_8)
#pop-options

let main () : I32.t =
     eq_mask_32 ()
 &&& eq_mask_8 ()
 &&& eq_mask_16 ()
 &&& eq_mask_64 ()
 &&& gte_mask_32 ()
 &&& gte_mask_64 ()
 &&& gte_mask_8_16 ()
 &&& mask_use_tests ()
 &&& minus_tests ()
