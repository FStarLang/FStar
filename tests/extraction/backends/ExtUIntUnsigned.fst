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

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
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
let lognot_tests () : I32.t =
     chk 21l (U16.eq (U16.lognot 0us) 65535us)
 &&& chk 22l (U32.eq (U32.lognot 0ul) 4294967295ul)
 &&& chk 23l (U64.eq (U64.lognot 0uL) 18446744073709551615uL)
 &&& chk 26l (U32.eq (U32.logand u32_max 0x0000ff00ul) 0x0000ff00ul)
 &&& chk 27l (U32.eq (U32.logxor u32_max 0x0000ff00ul) 0xffff00fful)
 &&& chk 28l (U32.eq (U32.logor  0ul 0x0000ff00ul) 0x0000ff00ul)

/// Shifts are *logical* for unsigned values, and the narrow widths must not
/// keep the bits that overflow past the top.
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
 &&& shift_tests ()
 &&& div_tests ()
 &&& cmp_tests ()
