module Wide128

open FStar.All

module U   = FStar.UInt128
module I   = FStar.Int128
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module I64 = FStar.Int64
module I32 = FStar.Int32

(* Section 119.  [FStar.UInt128] and [FStar.Int128] as [unsigned __int128] and
   [__int128].

   Everything here is checked by the program: a grep can see that the type
   came out as [unsigned __int128], but not that [gte_mask] has its operands
   the right way round or that [shift_arithmetic_right] is arithmetic.  The
   ones that matter most are the ones a 64-bit answer would also satisfy --
   [mul_wide] of two values whose product needs 65 bits and up, and a shift
   across the halfway line -- because those are what says the width is real
   and not a pair of [uint64_t]s. *)

(* A constant that needs both halves.  C has no 128-bit literal, so this is
   the one that has to be assembled. *)
let big : U.t = U.uint_to_t 0x123456789abcdef0fedcba9876543210

let ones : U.t = U.lognot (U.uint_to_t 0)
let uzero : U.t = U.uint_to_t 0

let main () : ML I32.t =
  (* 2^64 - 1, and 2^64, which is the first value a [uint64_t] does not hold.
     If either the type or the addition were 64 bits wide this would wrap. *)
  let a = U.uint64_to_uint128 0xffffffffffffffffuL in
  let b = U.mul_wide 0x100000000uL 0x100000000uL in
  let ok1 = U.eq (U.add_mod a (U.uint64_to_uint128 1uL)) b in

  (* The widening multiplication in full: (2^64-1)^2 = 2^128 - 2^65 + 1. *)
  let ok2 = U.eq (U.mul_wide 0xffffffffffffffffuL 0xffffffffffffffffuL)
                 (U.uint_to_t 340282366920938463426481119284349108225) in
  let ok3 = U.eq (U.mul32 0x100000000uL 4ul) (U.uint_to_t 0x400000000) in

  (* Both halves of the assembled constant, reached by a shift across the
     boundary and by the truncating conversion. *)
  let ok4 = U64.eq (U.uint128_to_uint64 big) 0xfedcba9876543210uL in
  let ok5 = U64.eq (U.uint128_to_uint64 (U.shift_right big 64ul))
                   0x123456789abcdef0uL in
  let ok6 = U.eq (U.shift_left (U.uint64_to_uint128 1uL) 127ul)
                 (U.uint_to_t 170141183460469231731687303715884105728) in

  (* The constant-time masks, which are [val]s at this width and so are the
     rule's own rather than the interface's. *)
  let ok7 = U.eq (U.eq_mask big big) ones && U.eq (U.eq_mask a b) uzero in
  let ok8 = U.eq (U.gte_mask b a) ones && U.eq (U.gte_mask a b) uzero in

  let ok9 = U.eq (U.logor (U.logand big uzero) (U.logxor big big)) uzero in

  (* Signed.  [lognot zero] is -1 without an arithmetic precondition, and an
     arithmetic shift of -1 is -1 -- a logical one would give a very large
     positive number, which is the whole distinction. *)
  let m1 = I.lognot I.zero in
  let ok10 = I.eq (I.shift_arithmetic_right m1 3ul) m1 in
  let ok11 = I.lt (I.mul_wide (-3L) 4L) I.zero in
  (* 0x7fff...^2 needs 126 bits: at 64 this is a wrap, and a wrap here is
     negative. *)
  let ok12 = I.gt (I.mul_wide 0x7fffffffffffffffL 0x7fffffffffffffffL) I.zero in

  if ok1 && ok2 && ok3 && ok4 && ok5 && ok6 &&
     ok7 && ok8 && ok9 && ok10 && ok11 && ok12
  then 0l else 1l
