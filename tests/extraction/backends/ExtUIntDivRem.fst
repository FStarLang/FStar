module ExtUIntDivRem

/// Unsigned division and remainder at every width.
///
/// The interesting failure mode is a backend that implements `div`/`rem` with
/// a *signed* machine division. For every operand whose top bit is set the two
/// disagree: read as unsigned, `0xFFFFFFFF / 3` is 1431655765; read as signed
/// it is `-1 / 3 = 0`. That is a silent wrong-value bug (severity 2), not a
/// crash, so nothing but a runtime comparison will catch it.
///
/// The narrow widths add a second hazard: C promotes `uint8_t` and `uint16_t`
/// operands to `int` before dividing. That happens to be harmless for division
/// (the promotion is value-preserving for unsigned types narrower than `int`),
/// but only as long as the backend does not insert a cast to the *signed*
/// same-width type on the way, which is exactly what a careless
/// narrowing-cast optimisation would do.
///
/// All divisors are top-level constants so that extraction cannot constant-fold
/// the division away and turn the check into `true == true`.

module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let u8_max  : U8.t  = 255uy
let u16_max : U16.t = 65535us
let u32_max : U32.t = 4294967295ul
let u64_max : U64.t = 18446744073709551615uL

(* Top bit set, nothing else: the smallest value a signed reading gets wrong. *)
let u8_hi  : U8.t  = 128uy
let u16_hi : U16.t = 32768us
let u32_hi : U32.t = 2147483648ul
let u64_hi : U64.t = 9223372036854775808uL

let d3_8   : U8.t  = 3uy
let d7_16  : U16.t = 7us
let d3_32  : U32.t = 3ul
let d7_32  : U32.t = 7ul
let d3_64  : U64.t = 3uL
let d2_32  : U32.t = 2ul

let one_8  : U8.t  = 1uy
let one_16 : U16.t = 1us
let one_32 : U32.t = 1ul
let one_64 : U64.t = 1uL
let zero_32 : U32.t = 0ul

(* Second copies, so that `x / x` is not written as a self-comparison and
   gcc's -Wtautological-compare stays quiet. *)
let u32_max' : U32.t = 4294967295ul
let u64_max' : U64.t = 18446744073709551615uL

/// Operands whose top bit is set. A signed division gets every one of these
/// wrong, and gets them wrong *quietly*.
let top_bit_tests () : I32.t =
     (* signed: -1 / 3 = 0 *)
     chk 1l (U32.eq (U32.div u32_max d3_32) 1431655765ul)
 &&& chk 2l (U64.eq (U64.div u64_max d3_64) 6148914691236517205uL)
 &&& chk 3l (U16.eq (U16.div u16_max d7_16) 9362us)
 &&& chk 4l (U8.eq  (U8.div  u8_max  d3_8)  85uy)
     (* signed: -2^31 / 2 = -2^30, i.e. 0xC0000000 read back as unsigned *)
 &&& chk 5l (U32.eq (U32.div u32_hi d2_32) 1073741824ul)
 &&& chk 6l (U64.eq (U64.div u64_hi d3_64) 3074457345618258602uL)
 &&& chk 7l (U16.eq (U16.div u16_hi d7_16) 4681us)
 &&& chk 8l (U8.eq  (U8.div  u8_hi  d3_8)  42uy)

/// The same operands under `rem`. C's `%` follows the sign of the dividend, so
/// a signed implementation can even produce a *negative* remainder here, which
/// read back as unsigned is enormous.
let top_bit_rem_tests () : I32.t =
     (* signed: -1 % 7 = -1 *)
     chk 10l (U32.eq (U32.rem u32_max d7_32) 3ul)
 &&& chk 11l (U64.eq (U64.rem u64_max d3_64) 0uL)
 &&& chk 12l (U16.eq (U16.rem u16_max d7_16) 1us)
 &&& chk 13l (U8.eq  (U8.rem  u8_max  d3_8)  0uy)
 &&& chk 14l (U32.eq (U32.rem u32_hi d3_32) 2ul)
 &&& chk 15l (U64.eq (U64.rem u64_hi d3_64) 2uL)
 &&& chk 16l (U16.eq (U16.rem u16_hi d7_16) 1us)
 &&& chk 17l (U8.eq  (U8.rem  u8_hi  d3_8)  2uy)

/// Identity divisors and self-division: cheap, but they are exactly the cases
/// a peephole optimisation is most likely to rewrite incorrectly.
let identity_tests () : I32.t =
     chk 20l (U32.eq (U32.div u32_max one_32) u32_max)
 &&& chk 21l (U64.eq (U64.div u64_max one_64) u64_max)
 &&& chk 22l (U16.eq (U16.div u16_max one_16) u16_max)
 &&& chk 23l (U8.eq  (U8.div  u8_max  one_8)  u8_max)
 &&& chk 24l (U32.eq (U32.rem u32_max one_32) 0ul)
 &&& chk 25l (U32.eq (U32.div u32_max u32_max') one_32)
 &&& chk 26l (U64.eq (U64.div u64_max u64_max') one_64)
 &&& chk 27l (U32.eq (U32.rem u32_max u32_max') 0ul)
     (* a dividend smaller than the divisor truncates to zero *)
 &&& chk 28l (U32.eq (U32.div one_32 u32_max) 0ul)
 &&& chk 29l (U32.eq (U32.rem one_32 u32_max) one_32)
 &&& chk 30l (U32.eq (U32.div zero_32 u32_max) 0ul)

/// `(a / b) * b + a % b = a` has to hold for every backend. Stated with
/// `mul_mod` rather than `mul` so that no overflow side condition is needed.
#push-options "--z3rlimit 60"
let euclid_tests () : I32.t =
     chk 40l (U32.eq (U32.add (U32.mul_mod (U32.div u32_max d7_32) d7_32)
                              (U32.rem u32_max d7_32))
                     u32_max)
 &&& chk 41l (U64.eq (U64.add (U64.mul_mod (U64.div u64_max d3_64) d3_64)
                              (U64.rem u64_max d3_64))
                     u64_max)
 &&& chk 42l (U8.eq  (U8.add  (U8.mul_mod  (U8.div  u8_hi d3_8) d3_8)
                              (U8.rem u8_hi d3_8))
                     u8_hi)
#pop-options

let main () : I32.t =
     top_bit_tests ()
 &&& top_bit_rem_tests ()
 &&& identity_tests ()
 &&& euclid_tests ()
