module ExtIntSigned

/// Signed machine integers: FStar.Int8 / Int16 / Int32 / Int64.
///
/// The interesting cases are the ones where the three backends implement the
/// operation with *different* primitives:
///   - OCaml uses Stdint (Int8/Int16 are emulated on top of wider words),
///   - C uses native `int8_t`/... arithmetic, subject to integer promotion,
///   - Rust uses `wrapping_div`/`wrapping_rem`/`wrapping_shr`.
/// F* specifies division as truncating towards zero and the remainder as
/// having the sign of the dividend, and `shift_arithmetic_right` as a
/// sign-extending shift. All of that has to hold at runtime.

module I8  = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module U32 = FStar.UInt32

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

(* Operands are top-level names so that extraction cannot constant-fold the
   operations below; see README.md. *)
let m7  : I32.t = -7l
let m7' : I32.t = -7l   (* a second copy: writing `m7 <= m7` makes the C
                           compiler reject the code with -Wtautological-compare *)
let p7  : I32.t =  7l
let m2  : I32.t = -2l
let p2  : I32.t =  2l
let i32_min : I32.t = -2147483648l
let i32_max : I32.t =  2147483647l
let one32 : U32.t = 1ul
let w31   : U32.t = 31ul

let m7_8 : I8.t = -7y
let p2_8 : I8.t = 2y
let i8_min : I8.t = -128y
let i8_max : I8.t = 127y

let m7_16 : I16.t = -7s
let p2_16 : I16.t = 2s
let i16_min : I16.t = -32768s

let m7_64 : I64.t = -7L
let p2_64 : I64.t = 2L
let i64_min : I64.t = -9223372036854775808L

let m1_8  : I8.t  = -1y
let m1_16 : I16.t = -1s
let m1_32 : I32.t = -1l
let m1_64 : I64.t = -1L

let m8_8  : I8.t  = -8y
let m8_16 : I16.t = -8s
let m8_32 : I32.t = -8l
let m8_64 : I64.t = -8L

let mask8 : I8.t = 0x5ay
let mask32 : I32.t = 0x5a5a5a5al

/// Division truncates towards zero and the remainder takes the sign of the
/// dividend: (-7)/2 = -3 and (-7)%2 = -1 (NOT -4 and 1).
let div_rem_32 () : I32.t =
     chk 1l (I32.eq (I32.div m7 p2) (-3l))
 &&& chk 2l (I32.eq (I32.rem m7 p2) (-1l))
 &&& chk 3l (I32.eq (I32.div p7 m2) (-3l))
 &&& chk 4l (I32.eq (I32.rem p7 m2) 1l)
 &&& chk 5l (I32.eq (I32.div m7 m2) 3l)
 &&& chk 6l (I32.eq (I32.rem m7 m2) (-1l))
 &&& chk 7l (I32.eq (I32.div p7 p2) 3l)
 &&& chk 8l (I32.eq (I32.rem p7 p2) 1l)
     (* a * (a/b) + a%b = a must hold *)
 &&& chk 9l (I32.eq (I32.add (I32.mul (I32.div m7 p2) p2) (I32.rem m7 p2)) m7)

let div_rem_small () : I32.t =
     chk 10l (I8.eq (I8.div m7_8 p2_8) (-3y))
 &&& chk 11l (I8.eq (I8.rem m7_8 p2_8) (-1y))
 &&& chk 12l (I16.eq (I16.div m7_16 p2_16) (-3s))
 &&& chk 13l (I16.eq (I16.rem m7_16 p2_16) (-1s))
 &&& chk 14l (I64.eq (I64.div m7_64 p2_64) (-3L))
 &&& chk 15l (I64.eq (I64.rem m7_64 p2_64) (-1L))

/// Logical operations are specified on the two's complement bit vector, so
/// they must produce the F*-predicted value even for negative operands.
let logic_tests () : I32.t =
     chk 40l (I32.eq (I32.lognot m1_32) 0l)
 &&& chk 41l (I32.eq (I32.lognot 0l) (-1l))
 &&& chk 42l (I8.eq  (I8.lognot  m1_8)  0y)
 &&& chk 43l (I16.eq (I16.lognot m1_16) 0s)
 &&& chk 44l (I64.eq (I64.lognot m1_64) 0L)
 &&& chk 45l (I32.eq (I32.logand m1_32 mask32) mask32)
 &&& chk 46l (I32.eq (I32.logor  0l mask32) mask32)
 &&& chk 47l (I32.eq (I32.logxor mask32 mask32) 0l)
 &&& chk 48l (I32.eq (I32.logxor m1_32 mask32) (I32.lognot mask32))
 &&& chk 49l (I8.eq  (I8.logand m1_8 mask8) mask8)
     (* logand of a negative with a small positive keeps low bits *)
 &&& chk 50l (I32.eq (I32.logand m8_32 7l) 0l)
 &&& chk 51l (I32.eq (I32.logand m7 7l) 1l)

/// Non-wrapping arithmetic at the extremes of the range.
let arith_tests () : I32.t =
     chk 60l (I32.eq (I32.add i32_max (-1l)) 2147483646l)
 &&& chk 61l (I32.eq (I32.sub i32_min (-1l)) (-2147483647l))
 &&& chk 62l (I32.eq (I32.mul m7 m2) 14l)
 &&& chk 63l (I8.eq  (I8.mul  m7_8 p2_8) (-14y))
 &&& chk 64l (I16.eq (I16.mul m7_16 p2_16) (-14s))
 &&& chk 65l (I64.eq (I64.mul m7_64 p2_64) (-14L))
     (* Int8 multiplication must not be computed at `int` width and kept wide *)
 &&& chk 66l (I8.eq (I8.mul 11y 11y) 121y)
 &&& chk 67l (I8.eq (I8.sub i8_min 0y) (-128y))
 &&& chk 68l (I8.eq (I8.add i8_max 0y) 127y)

/// Comparisons on negative values, at every width.
let cmp_tests () : I32.t =
     chk 70l (I32.lt m7 p2)
 &&& chk 71l (I32.gt p2 m7)
 &&& chk 72l (not (I32.lt p2 m7))
 &&& chk 73l (I32.lte m7 m7')
 &&& chk 74l (I32.gte m7 m7')
 &&& chk 76l (I32.lt i32_min i32_max)
 &&& chk 77l (I8.lt  i8_min i8_max)
 &&& chk 78l (I16.lt m7_16 p2_16)
 &&& chk 79l (I64.lt i64_min 0L)
     (* Int8 comparison must be signed, not accidentally done on a
        zero-extended byte: -1 < 1 *)
 &&& chk 80l (I8.lt m1_8 1y)
 &&& chk 81l (I16.lt m1_16 1s)

let main () : I32.t =
     div_rem_32 ()
 &&& div_rem_small ()
 &&& logic_tests ()
 &&& arith_tests ()
 &&& cmp_tests ()
