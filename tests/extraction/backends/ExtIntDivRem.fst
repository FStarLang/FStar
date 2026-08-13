module ExtIntDivRem

/// Signed division and remainder at every width. This is the F* analogue of
/// karamel/test/Division.fst, extended to all four widths and to both
/// operands' signs.
///
/// `FStar.Int` specifies division as *truncation towards zero* and states that
/// "remainders have the same sign as the dividend" -- i.e. C99 semantics, and
/// also OCaml's. A backend that lowers `div` to a floored (Euclidean) division
/// instead, which is what Python, Haskell's `div` and Z3's `div` all do,
/// differs on every quotient with a negative operand:
///
///   truncating: -7 / 3 = -2, -7 % 3 = -1
///   flooring:   -7 / 3 = -3, -7 % 3 =  2
///
/// so the four sign combinations of each operation are all checked separately.
/// `-1` is the divisor that matters most: `INT_MIN / -1` overflows and is
/// undefined in C, so F* rules it out and we stay away from it, but
/// `x / -1 = -x` for every other `x` and is a common place to get the sign
/// wrong.

module I8  = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let p7  : I32.t = 7l
let m7  : I32.t = -7l
let p3  : I32.t = 3l
let m3  : I32.t = -3l
let mone : I32.t = -1l
let p1   : I32.t = 1l

let p7_8  : I8.t  = 7y
let m7_8  : I8.t  = -7y
let p3_8  : I8.t  = 3y
let m3_8  : I8.t  = -3y

let p7_16 : I16.t = 7s
let m7_16 : I16.t = -7s
let p3_16 : I16.t = 3s
let m3_16 : I16.t = -3s

let p7_64 : I64.t = 7L
let m7_64 : I64.t = -7L
let p3_64 : I64.t = 3L
let m3_64 : I64.t = -3L

let i8_min  : I8.t  = -128y
let i16_min : I16.t = -32768s
let i32_min : I32.t = -2147483648l
let i64_min : I64.t = -9223372036854775808L
let i32_max : I32.t = 2147483647l

/// All four sign combinations at 32 bits. Under flooring division checks 2, 3,
/// 6 and 7 all come out one lower.
let sign_tests () : I32.t =
     chk 1l (I32.eq (I32.div p7 p3) 2l)
 &&& chk 2l (I32.eq (I32.div m7 p3) (-2l))
 &&& chk 3l (I32.eq (I32.div p7 m3) (-2l))
 &&& chk 4l (I32.eq (I32.div m7 m3) 2l)
     (* the remainder takes the sign of the *dividend*, not the divisor *)
 &&& chk 5l (I32.eq (I32.rem p7 p3) 1l)
 &&& chk 6l (I32.eq (I32.rem m7 p3) (-1l))
 &&& chk 7l (I32.eq (I32.rem p7 m3) 1l)
 &&& chk 8l (I32.eq (I32.rem m7 m3) (-1l))

/// The same at the other three widths. The narrow ones are the ones C promotes
/// to `int` before dividing, so the backend has to narrow the result back.
let width_tests () : I32.t =
     chk 10l (I8.eq (I8.div m7_8 p3_8) (-2y))
 &&& chk 11l (I8.eq (I8.rem m7_8 p3_8) (-1y))
 &&& chk 12l (I8.eq (I8.div p7_8 m3_8) (-2y))
 &&& chk 13l (I8.eq (I8.rem p7_8 m3_8) 1y)
 &&& chk 14l (I16.eq (I16.div m7_16 p3_16) (-2s))
 &&& chk 15l (I16.eq (I16.rem m7_16 p3_16) (-1s))
 &&& chk 16l (I16.eq (I16.div p7_16 m3_16) (-2s))
 &&& chk 17l (I16.eq (I16.rem p7_16 m3_16) 1s)
 &&& chk 18l (I64.eq (I64.div m7_64 p3_64) (-2L))
 &&& chk 19l (I64.eq (I64.rem m7_64 p3_64) (-1L))
 &&& chk 20l (I64.eq (I64.div p7_64 m3_64) (-2L))
 &&& chk 21l (I64.eq (I64.rem p7_64 m3_64) 1L)

/// Dividing by -1 negates. `INT_MIN / -1` is deliberately absent: it overflows
/// and F* rejects it, which is itself worth recording -- a backend must not
/// "optimise" `x / -1` into something that admits it.
let neg_one_tests () : I32.t =
     chk 30l (I32.eq (I32.div p7 mone) (-7l))
 &&& chk 31l (I32.eq (I32.div m7 mone) 7l)
 &&& chk 32l (I32.eq (I32.rem p7 mone) 0l)
 &&& chk 33l (I32.eq (I32.rem m7 mone) 0l)
 &&& chk 34l (I32.eq (I32.div i32_max mone) (-2147483647l))
 &&& chk 35l (I32.eq (I32.div p7 p1) 7l)
 &&& chk 36l (I32.eq (I32.div m7 p1) (-7l))

/// The most negative value is where sign handling breaks. Dividing it by a
/// positive divisor is well defined; the quotient must stay negative and must
/// not be computed through an unsigned intermediate, which would make it huge
/// and positive.
#push-options "--z3rlimit 60"
let min_tests () : I32.t =
     chk 40l (I32.lt (I32.div i32_min p3) 0l)
 &&& chk 41l (I32.eq (I32.div i32_min p3) (-715827882l))
 &&& chk 42l (I32.eq (I32.rem i32_min p3) (-2l))
 &&& chk 43l (I8.eq  (I8.div  i8_min  p3_8)  (-42y))
 &&& chk 44l (I8.eq  (I8.rem  i8_min  p3_8)  (-2y))
 &&& chk 45l (I16.eq (I16.div i16_min p3_16) (-10922s))
 &&& chk 46l (I16.eq (I16.rem i16_min p3_16) (-2s))
 &&& chk 47l (I64.eq (I64.div i64_min p3_64) (-3074457345618258602L))
 &&& chk 48l (I64.eq (I64.rem i64_min p3_64) (-2L))
#pop-options

/// `(a / b) * b + a % b = a` in all four sign combinations.
#push-options "--z3rlimit 60"
let euclid_tests () : I32.t =
     chk 50l (I32.eq (I32.add (I32.mul (I32.div m7 p3) p3) (I32.rem m7 p3)) m7)
 &&& chk 51l (I32.eq (I32.add (I32.mul (I32.div p7 m3) m3) (I32.rem p7 m3)) p7)
 &&& chk 52l (I32.eq (I32.add (I32.mul (I32.div m7 m3) m3) (I32.rem m7 m3)) m7)
 &&& chk 53l (I32.eq (I32.add (I32.mul (I32.div p7 p3) p3) (I32.rem p7 p3)) p7)
#pop-options

let main () : I32.t =
     sign_tests ()
 &&& width_tests ()
 &&& neg_one_tests ()
 &&& min_tests ()
 &&& euclid_tests ()
