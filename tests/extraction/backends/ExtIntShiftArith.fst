module ExtIntShiftArith

/// `FStar.IntN.shift_arithmetic_right`: a sign-extending right shift.
///
/// This is the one machine-integer operation that Karamel does *not* express
/// with a `Krml` opcode: `mk_op` in src/extraction/FStarC.Extraction.Krml.fst
/// has no case for `shift_arithmetic_right`, so the operation survives
/// extraction as a call to `FStar_IntN_shift_arithmetic_right`. For C that is
/// fine -- Karamel hand-writes those four functions in
/// karamel/include/krml/fstar_int.h and whitelists them in
/// karamel/lib/Helpers.ml (`builtin_names`) -- but the Rust backend has no
/// such fallback (see the NO_RUST entry in the Makefile).
///
/// F* specifies the operation on the two's complement bit vector, so the sign
/// bit must be replicated; C's `>>` on a negative signed value is only
/// implementation-defined, hence the dedicated implementation.

module I8  = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module U32 = FStar.UInt32

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let one32 : U32.t = 1ul
let w31   : U32.t = 31ul

let i32_min : I32.t = -2147483648l
let i8_min  : I8.t  = -128y
let i16_min : I16.t = -32768s
let i64_min : I64.t = -9223372036854775808L

let m1_8  : I8.t  = -1y
let m1_16 : I16.t = -1s
let m1_32 : I32.t = -1l
let m1_64 : I64.t = -1L

let m8_8  : I8.t  = -8y
let m8_16 : I16.t = -8s
let m8_32 : I32.t = -8l
let m8_64 : I64.t = -8L

/// Arithmetic shift right must sign-extend at every width. Note Int8/Int16 are
/// emulated in OCaml's Stdint and promoted to `int` in C, so this is exactly
/// where the widths can disagree.
let main () : I32.t =
     chk 20l (I32.eq (I32.shift_arithmetic_right m8_32 one32) (-4l))
 &&& chk 21l (I8.eq  (I8.shift_arithmetic_right  m8_8  one32) (-4y))
 &&& chk 22l (I16.eq (I16.shift_arithmetic_right m8_16 one32) (-4s))
 &&& chk 23l (I64.eq (I64.shift_arithmetic_right m8_64 one32) (-4L))
     (* shifting -1 right by anything stays -1 (all sign bits) *)
 &&& chk 24l (I32.eq (I32.shift_arithmetic_right m1_32 w31) (-1l))
 &&& chk 25l (I8.eq  (I8.shift_arithmetic_right  m1_8  7ul) (-1y))
 &&& chk 26l (I16.eq (I16.shift_arithmetic_right m1_16 15ul) (-1s))
 &&& chk 27l (I64.eq (I64.shift_arithmetic_right m1_64 63ul) (-1L))
     (* INT_MIN >> 1 sign-extends to INT_MIN/2 *)
 &&& chk 28l (I32.eq (I32.shift_arithmetic_right i32_min one32) (-1073741824l))
 &&& chk 29l (I8.eq  (I8.shift_arithmetic_right  i8_min  one32) (-64y))
 &&& chk 30l (I16.eq (I16.shift_arithmetic_right i16_min one32) (-16384s))
 &&& chk 31l (I64.eq (I64.shift_arithmetic_right i64_min one32) (-4611686018427387904L))
     (* shifting by 0 is the identity, including for negatives *)
 &&& chk 32l (I32.eq (I32.shift_arithmetic_right m8_32 0ul) (-8l))

