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

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
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
///
/// `chk` requires each check to be *provably* true. F* specifies
/// `shift_arithmetic_right` on the two's complement bit vector and provides no
/// value lemma for it (see FINDINGS.md #13), so the expected results are
/// established bit by bit with `FStar.Int.nth_lemma`, whose `nth` SMT patterns
/// let the solver compare the two vectors. Lemmas are erased at extraction, so
/// the runtime checks are unchanged.
module I = FStar.Int

#push-options "--z3rlimit 60"
let sar_32 () : I32.t =
  I.nth_lemma #32 (I.shift_arithmetic_right #32 (-8) 1) (-4);
  I.nth_lemma #32 (I.shift_arithmetic_right #32 (-1) 31) (-1);
  I.nth_lemma #32 (I.shift_arithmetic_right #32 (-8) 0) (-8);
     chk 20l (I32.eq (I32.shift_arithmetic_right m8_32 one32) (-4l))
     (* shifting -1 right by anything stays -1 (all sign bits) *)
 &&& chk 24l (I32.eq (I32.shift_arithmetic_right m1_32 w31) (-1l))
     (* shifting by 0 is the identity, including for negatives *)
 &&& chk 32l (I32.eq (I32.shift_arithmetic_right m8_32 0ul) (-8l))

let sar_8 () : I32.t =
  I.nth_lemma #8 (I.shift_arithmetic_right #8 (-8) 1) (-4);
  I.nth_lemma #8 (I.shift_arithmetic_right #8 (-1) 7) (-1);
     chk 21l (I8.eq (I8.shift_arithmetic_right m8_8 one32) (-4y))
 &&& chk 25l (I8.eq (I8.shift_arithmetic_right m1_8  7ul) (-1y))


let sar_16 () : I32.t =
  I.nth_lemma #16 (I.shift_arithmetic_right #16 (-8) 1) (-4);
  I.nth_lemma #16 (I.shift_arithmetic_right #16 (-1) 15) (-1);
     chk 22l (I16.eq (I16.shift_arithmetic_right m8_16 one32) (-4s))
 &&& chk 26l (I16.eq (I16.shift_arithmetic_right m1_16 15ul) (-1s))

#pop-options

/// INT_MIN is the interesting extreme: C's `>>` on a negative signed value is
/// only implementation-defined, so a backend that shifts logically would drop
/// the sign. Comparing against the full expected value costs the solver
/// minutes here (`nth_lemma` has to match all n bits of an extreme literal),
/// so this checks the property that actually distinguishes an arithmetic from
/// a logical shift, and needs only the top bit: the result is still negative.
/// `shift_arithmetic_right_lemma_1` gives `nth (sar a s) 0 = nth a 0`, and
/// `sign_bit_negative` turns that back into a sign.
#push-options "--z3rlimit 60"
let sar_int_min () : I32.t =
  I.shift_arithmetic_right_lemma_1 #32 (I32.v i32_min) 1 0;
  I.sign_bit_negative #32 (I32.v i32_min);
  I.sign_bit_negative #32 (I.shift_arithmetic_right #32 (I32.v i32_min) 1);
  I.shift_arithmetic_right_lemma_1 #8 (I8.v i8_min) 1 0;
  I.sign_bit_negative #8 (I8.v i8_min);
  I.sign_bit_negative #8 (I.shift_arithmetic_right #8 (I8.v i8_min) 1);
  I.shift_arithmetic_right_lemma_1 #16 (I16.v i16_min) 1 0;
  I.sign_bit_negative #16 (I16.v i16_min);
  I.sign_bit_negative #16 (I.shift_arithmetic_right #16 (I16.v i16_min) 1);
  I.shift_arithmetic_right_lemma_1 #64 (I64.v i64_min) 1 0;
  I.sign_bit_negative #64 (I64.v i64_min);
  I.sign_bit_negative #64 (I.shift_arithmetic_right #64 (I64.v i64_min) 1);
     chk 28l (I32.lt (I32.shift_arithmetic_right i32_min one32) 0l)
 &&& chk 29l (I8.lt  (I8.shift_arithmetic_right  i8_min  one32) 0y)
 &&& chk 30l (I16.lt (I16.shift_arithmetic_right i16_min one32) 0s)
 &&& chk 31l (I64.lt (I64.shift_arithmetic_right i64_min one32) 0L)
#pop-options

#push-options "--z3rlimit 200"
let sar_64 () : I32.t =
  I.nth_lemma #64 (I.shift_arithmetic_right #64 (-8) 1) (-4);
  I.nth_lemma #64 (I.shift_arithmetic_right #64 (-1) 63) (-1);
     chk 23l (I64.eq (I64.shift_arithmetic_right m8_64 one32) (-4L))
 &&& chk 27l (I64.eq (I64.shift_arithmetic_right m1_64 63ul) (-1L))

#pop-options

let main () : I32.t =
     sar_32 ()
 &&& sar_8 ()
 &&& sar_16 ()
 &&& sar_64 ()
 &&& sar_int_min ()

