module ExtUIntUnsigned

/// Unsigned machine integers: FStar.UInt8 / UInt16 / UInt32 / UInt64.
///
/// The point of interest is the `_mod` family (`add_mod`, `sub_mod`,
/// `mul_mod`, spelled `+%^`, `-%^`, `*%^`), which is *specified* to wrap
/// modulo 2^n. At the narrow widths this is where C's integer promotion rules
/// bite: `uint8_t * uint8_t` is computed at `int` width in C, so the truncation
/// back to 8 bits has to be re-introduced by the backend. In OCaml, UInt8 is a
/// plain `int` masked by hand while UInt16/32/64 are Stdint values, so the two
/// code paths are completely different implementations of the same spec.

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

let c200 : U8.t = 200uy
let c3   : U8.t = 3uy
let c1_8 : U8.t = 1uy
let c0_8 : U8.t = 0uy

let c7   : U32.t = 7ul
let c2   : U32.t = 2ul
let c7'  : U32.t = 7ul

/// Wraparound must happen at the declared width, not at C's `int` width.
let wrap_tests () : I32.t =
     chk 1l (U8.eq (U8.add_mod u8_max c1_8) 0uy)
 &&& chk 2l (U8.eq (U8.sub_mod c0_8 c1_8) 255uy)
     (* 200 * 3 = 600; 600 mod 256 = 88 *)
 &&& chk 3l (U8.eq (U8.mul_mod c200 c3) 88uy)
 &&& chk 4l (U16.eq (U16.add_mod u16_max 1us) 0us)
 &&& chk 5l (U16.eq (U16.sub_mod 0us 1us) 65535us)
     (* 60000 * 3 = 180000; 180000 mod 65536 = 48928 *)
 &&& chk 6l (U16.eq (U16.mul_mod 60000us 3us) 48928us)
 &&& chk 7l (U32.eq (U32.add_mod u32_max 1ul) 0ul)
 &&& chk 8l (U32.eq (U32.sub_mod 0ul 1ul) 4294967295ul)
     (* 3000000000 * 3 = 9000000000; mod 2^32 = 410065408 *)
 &&& chk 9l (U32.eq (U32.mul_mod 3000000000ul 3ul) 410065408ul)
 &&& chk 10l (U64.eq (U64.add_mod u64_max 1uL) 0uL)
 &&& chk 11l (U64.eq (U64.sub_mod 0uL 1uL) 18446744073709551615uL)
 &&& chk 12l (U64.eq (U64.mul_mod 12297829382473034410uL 3uL) 18446744073709551614uL)

/// `lognot` must complement all n bits and nothing more, i.e. the result has
/// to be truncated back to the declared width. (UInt8 is broken in the OCaml
/// backend; that case lives in ExtUInt8Lognot.fst.)
/// `chk` demands a *proof* that each check holds. F* cannot evaluate a general
/// 32-bit bitwise operation on concrete values (FINDINGS.md #13), so the
/// expected values come from the `FStar.UInt` lemmas: `lognot 0 = ones`,
/// `logand a ones = a`, `logor a 0 = a`, and `logxor a ones = lognot a`. The
/// check 27 is stated relationally (`logxor a ones` must agree with `lognot a`)
/// because pinning the literal result of a general 32-bit operation is out of
/// reach for the solver; `general_tests` below keeps literal-valued coverage at
/// a width where F* *can* compute. All of it is erased at extraction.
#push-options "--z3rlimit 60"
let lognot_tests () : I32.t =
  U.lognot_lemma_1 #16; U.lognot_lemma_1 #32; U.lognot_lemma_1 #64;
  U.logand_lemma_2 #32 0x0000ff00; U.logand_commutative #32 (U.ones 32) 0x0000ff00;
  U.logor_lemma_1 #32 0x0000ff00;  U.logor_commutative #32 0x0000ff00 (U.zero 32);
  U.logxor_lemma_2 #32 0x0000ff00; U.logxor_commutative #32 (U.ones 32) 0x0000ff00;
     chk 21l (U16.eq (U16.lognot 0us) 65535us)
 &&& chk 22l (U32.eq (U32.lognot 0ul) 4294967295ul)
 &&& chk 23l (U64.eq (U64.lognot 0uL) 18446744073709551615uL)
 &&& chk 26l (U32.eq (U32.logand u32_max 0x0000ff00ul) 0x0000ff00ul)
 &&& chk 27l (U32.eq (U32.logxor u32_max 0x0000ff00ul) (U32.lognot 0x0000ff00ul))
 &&& chk 28l (U32.eq (U32.logor  0ul 0x0000ff00ul) 0x0000ff00ul)
#pop-options

/// Bitwise operations on *general* operands, with the expected value written
/// out as a literal. Only 8-bit: F* can evaluate `FStar.UInt` at that width
/// (with enough fuel to unroll `to_vec`/`from_vec`), but not at 32 or 64.
#push-options "--fuel 20 --ifuel 20 --z3rlimit 200"
let general_tests () : I32.t =
  assert_norm (U.logand #8 0xf8 0x0f == 0x08);
  assert_norm (U.logor  #8 0xf0 0x0f == 0xff);
  assert_norm (U.logxor #8 0xf5 0x0f == 0xfa);
  assert_norm (U.lognot #8 0x0f == 0xf0);
     chk 70l (U8.eq (U8.logand 0xf8uy 0x0fuy) 0x08uy)
 &&& chk 71l (U8.eq (U8.logor  0xf0uy 0x0fuy) 0xffuy)
 &&& chk 72l (U8.eq (U8.logxor 0xf5uy 0x0fuy) 0xfauy)
 &&& chk 73l (U8.eq (U8.lognot 0x0fuy) 0xf0uy)
#pop-options

/// Shifts are *logical* for unsigned values, and the narrow widths must not
/// keep the bits that overflow past the top. `shift_left/right_value_lemma`
/// give `a * pow2 s % pow2 n` and `a / pow2 s`, so the checks are provable, but
/// the 64-bit ones make the solver reason about `pow2 64` and need a budget.
#push-options "--z3rlimit 120"
let shift_tests () : I32.t =
     chk 30l (U8.eq  (U8.shift_left  0x81uy 1ul) 0x02uy)
 &&& chk 31l (U8.eq  (U8.shift_right 0x81uy 1ul) 0x40uy)
 &&& chk 32l (U16.eq (U16.shift_left  0x8001us 1ul) 0x0002us)
 &&& chk 33l (U16.eq (U16.shift_right 0x8001us 1ul) 0x4000us)
 &&& chk 34l (U32.eq (U32.shift_left  0x80000001ul 1ul) 0x00000002ul)
 &&& chk 35l (U32.eq (U32.shift_right 0x80000001ul 1ul) 0x40000000ul)
 &&& chk 36l (U64.eq (U64.shift_right u64_max 63ul) 1uL)
 &&& chk 37l (U8.eq  (U8.shift_left  c1_8 7ul) 128uy)
 &&& chk 38l (U32.eq (U32.shift_left 1ul 31ul) 2147483648ul)
     (* a shift by zero is the identity *)
 &&& chk 39l (U8.eq  (U8.shift_right u8_max 0ul) 255uy)
 &&& chk 40l (U32.eq (U32.shift_left u32_max 0ul) 4294967295ul)
#pop-options

/// Division and remainder are the easy cases (both operands non-negative), but
/// they must not be signed: 0xFFFFFFFF / 2 is 0x7FFFFFFF, not 0.
let div_tests () : I32.t =
     chk 50l (U32.eq (U32.div c7 c2) 3ul)
 &&& chk 51l (U32.eq (U32.rem c7 c2) 1ul)
 &&& chk 52l (U32.eq (U32.div u32_max 2ul) 2147483647ul)
 &&& chk 53l (U32.eq (U32.rem u32_max 2ul) 1ul)
 &&& chk 54l (U8.eq  (U8.div  u8_max 2uy) 127uy)
 &&& chk 55l (U64.eq (U64.div u64_max 2uL) 9223372036854775807uL)
 &&& chk 56l (U16.eq (U16.div u16_max 2us) 32767us)

/// Comparisons must be unsigned: 0xFFFFFFFF is *greater* than 1, even though
/// the same bit pattern read as a signed int is -1.
let cmp_tests () : I32.t =
     chk 60l (U32.gt u32_max 1ul)
 &&& chk 61l (U32.lt 1ul u32_max)
 &&& chk 62l (U8.gt  u8_max 1uy)
 &&& chk 63l (U16.gt u16_max 1us)
 &&& chk 64l (U64.gt u64_max 1uL)
 &&& chk 65l (U32.lte c7 c7')
 &&& chk 66l (U32.gte c7 c7')
 &&& chk 67l (not (U32.lt c7 c2))

let main () : I32.t =
     wrap_tests ()
 &&& lognot_tests ()
 &&& general_tests ()
 &&& shift_tests ()
 &&& div_tests ()
 &&& cmp_tests ()
