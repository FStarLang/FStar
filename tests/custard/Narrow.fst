module Narrow

open FStar.All

module B = BF16Lib
module U32 = FStar.UInt32

(* Section 66.  binary16 declared here, bfloat16 in [BF16Lib], so one test
   covers both formats and both the same-module and cross-module lookups.

   Like [FloatOptIn], nothing is proved: the program checks its own answers.
   [sub] and [div] are not commutative, so an operand swap shows up here and
   would not show up in a grep for the emitted call. *)

[@@FStar.Attributes.custard_float 16]
assume val t : Type0

assume val add : t -> t -> t
assume val sub : t -> t -> t
assume val mul : t -> t -> t
assume val div : t -> t -> t
assume val lt  : t -> t -> bool
assume val lte : t -> t -> bool
assume val ieee_eq : t -> t -> bool
assume val of_int : Int64.t -> t
assume val of_literal : string -> t
assume val zero : t
assume val one : t

let main () : ML U32.t =
  (* binary16, exactly representable values. *)
  let a = of_literal "1.5" in
  let b = of_literal "2.25" in
  let ok1 = ieee_eq (add a b) (of_literal "3.75") in
  let ok2 = ieee_eq (mul a b) (of_literal "3.375") in
  let ok3 = lt (sub a b) zero in
  let ok4 = lte (div a b) (of_literal "0.6667") in
  let ok5 = ieee_eq (of_int 3L) (of_literal "3.0") in
  let ok6 = ieee_eq (add zero one) one in

  (* Rounding is the format's, not binary32's: 2049 is not representable in
     binary16 (11 significand bits), and ties-to-even sends it to 2048. *)
  let ok7 = ieee_eq (of_int 2049L) (of_literal "2048.0") in
  (* 65520 rounds up to 65536, which overflows binary16 -- so this is
     infinity, and infinity is not less than itself. *)
  let ok8 = not (lt (of_literal "70000.0") (of_literal "70000.0")) in

  (* bfloat16 has binary32's exponent, so 70000 is an ordinary finite value
     there, and only 8 significand bits, so 257 rounds to 256. *)
  let ok9  = B.ieee_eq (B.add (B.of_literal "1.5") (B.of_literal "2.25"))
                       (B.of_literal "3.75") in
  let ok10 = B.lt (B.sub (B.of_literal "1.5") (B.of_literal "2.25")) B.zero in
  let ok11 = B.ieee_eq (B.of_int 257L) (B.of_literal "256.0") in
  let ok12 = B.lt (B.of_literal "70000.0") (B.of_literal "80000.0") in
  let ok13 = B.ieee_eq (B.add B.zero B.one) B.one in

  if ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8
     && ok9 && ok10 && ok11 && ok12 && ok13
  then 0ul else 1ul
