module ExtIntCast

/// `FStar.Int.Cast`: conversions between machine integer widths.
///
/// Narrowing casts are the interesting ones. F* specifies them arithmetically
/// (`v x % pow2 k` for unsigned targets, `v x @% pow2 k` for signed ones), and
/// each backend implements them completely differently:
///   - OCaml goes through `Prims.int` (Zarith) and `%` / `@%`,
///   - C uses a native cast, which for signed targets is only
///     implementation-defined when the value does not fit,
///   - Rust uses `as`, which is defined to truncate.
/// A widening signed cast must sign-extend, and a signed-to-unsigned cast of
/// the same width must reinterpret the bits.

module I8  = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C   = FStar.Int.Cast

// int32_to_int8 / int64_to_int32 are marked deprecated in ulib because C only
// gives an implementation-defined result when the value is not representable;
// we test them anyway, since every backend we support truncates.
#set-options "--warn_error -288"

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let m1_8   : I8.t  = -1y
let m1_16  : I16.t = -1s
let m1_32  : I32.t = -1l
let m1_64  : I64.t = -1L
let m128_8 : I8.t  = -128y
let m300_32 : I32.t = -300l
let big32  : I32.t = 0x12345678l
let big64  : I64.t = 0x123456789abcdef0L
let u255   : U8.t  = 255uy
let u65535 : U16.t = 65535us
let u32max : U32.t = 4294967295ul
let u64big : U64.t = 0x123456789abcdef0uL

/// Widening: signed casts sign-extend, unsigned casts zero-extend.
let widening () : I32.t =
     chk 1l (I16.eq (C.int8_to_int16 m1_8) (-1s))
 &&& chk 2l (I32.eq (C.int8_to_int32 m1_8) (-1l))
 &&& chk 3l (I64.eq (C.int8_to_int64 m1_8) (-1L))
 &&& chk 4l (I32.eq (C.int16_to_int32 m1_16) (-1l))
 &&& chk 5l (I64.eq (C.int32_to_int64 m1_32) (-1L))
 &&& chk 6l (I32.eq (C.int8_to_int32 m128_8) (-128l))
 &&& chk 7l (U16.eq (C.uint8_to_uint16 u255) 255us)
 &&& chk 8l (U32.eq (C.uint8_to_uint32 u255) 255ul)
 &&& chk 9l (U64.eq (C.uint8_to_uint64 u255) 255uL)
 &&& chk 10l (U32.eq (C.uint16_to_uint32 u65535) 65535ul)
 &&& chk 11l (U64.eq (C.uint32_to_uint64 u32max) 4294967295uL)

/// Narrowing keeps the low bits. `-300 mod 256 = 212`, and read back as a
/// signed byte `212 - 256 = -44`.
let narrowing () : I32.t =
     chk 20l (U8.eq (C.uint32_to_uint8 u32max) 255uy)
 &&& chk 21l (U16.eq (C.uint32_to_uint16 u32max) 65535us)
 &&& chk 22l (U8.eq (C.uint16_to_uint8 u65535) 255uy)
 &&& chk 23l (U32.eq (C.uint64_to_uint32 u64big) 0x9abcdef0ul)
 &&& chk 24l (U16.eq (C.uint64_to_uint16 u64big) 0xdef0us)
 &&& chk 25l (U8.eq (C.uint64_to_uint8 u64big) 0xf0uy)
 &&& chk 26l (I8.eq (C.int32_to_int8 m300_32) (-44y))
 &&& chk 27l (I16.eq (C.int32_to_int16 m300_32) (-300s))
 &&& chk 28l (I8.eq (C.int32_to_int8 big32) 0x78y)
 &&& chk 29l (I16.eq (C.int32_to_int16 big32) 0x5678s)
 &&& chk 30l (I32.eq (C.int64_to_int32 big64) (-1698898192l))
 &&& chk 31l (I8.eq (C.int16_to_int8 (-300s)) (-44y))

/// Sign changes at the same width reinterpret the bit pattern.
let sign_changes () : I32.t =
     chk 40l (U8.eq (C.int8_to_uint8 m1_8) 255uy)
 &&& chk 41l (U16.eq (C.int16_to_uint16 m1_16) 65535us)
 &&& chk 42l (U32.eq (C.int32_to_uint32 m1_32) 4294967295ul)
 &&& chk 43l (U64.eq (C.int64_to_uint64 m1_64) 18446744073709551615uL)
 &&& chk 44l (I8.eq (C.uint8_to_int8 u255) (-1y))
 &&& chk 45l (I16.eq (C.uint16_to_int16 u65535) (-1s))
 &&& chk 46l (I32.eq (C.uint32_to_int32 u32max) (-1l))
 &&& chk 47l (U8.eq (C.int8_to_uint8 m128_8) 128uy)

/// Round trips: narrowing then widening must lose exactly the high bits.
let round_trips () : I32.t =
     chk 50l (U32.eq (C.uint8_to_uint32 (C.uint32_to_uint8 u32max)) 255ul)
 &&& chk 51l (I32.eq (C.int8_to_int32 (C.int32_to_int8 m300_32)) (-44l))
 &&& chk 52l (U64.eq (C.uint32_to_uint64 (C.uint64_to_uint32 u64big)) 0x9abcdef0uL)
 &&& chk 53l (I64.eq (C.int32_to_int64 (C.int64_to_int32 big64)) (-1698898192L))

let main () : I32.t =
     widening ()
 &&& narrowing ()
 &&& sign_changes ()
 &&& round_trips ()
