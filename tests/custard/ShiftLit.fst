module ShiftLit

(* Section 61.1.  A literal on the left of a shift keeps its cast.

   Section 59.3 removed a literal operand's cast on the argument that a
   binary operator's two operands share an IR type, so the other operand
   already says what the literal's type is.  A shift is the exception, and
   it is the one binary operator for which the premise is simply false:
   [U64.shift_left] takes a [U32.t] amount, so the operands do not share a
   type at all.  C agrees -- 6.5.7 promotes the two separately and gives the
   result the promoted type of the *left* operand, so the usual arithmetic
   conversions never run and the right operand cannot say anything about
   the result.

   Without the cast, [40 << n] is computed at [int]: at 64 bits a wrong
   value, at 32 bits undefined behaviour, and under [-Wall -Wextra -O2] not
   a single diagnostic.  [truncate] does not catch it, because it re-casts
   only at [Int8] and [Int16], where both operands promote to [int] anyway
   -- the bug is at exactly the widths it leaves alone.

   [pl] is the control and is the reason both are here: it must *keep* the
   section 59 improvement ([40 + n], no cast), since addition really does
   convert.  A fix that restored the cast for every operator would pass a
   test that only checked [sh].

   [main] checks its own answers, so the run is the assertion: before the
   fix this program returned 1. *)

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32
open FStar.All

let sh (n : U32.t{U32.v n < 64}) : U64.t = U64.shift_left 40uL n
let pl (n : U64.t) : U64.t = U64.add_mod 40uL n

let main () : ML I32.t =
  let n = 32ul in
  if U64.eq (sh n) 171798691840uL && U64.eq (pl 4uL) 44uL then 0l else 1l
