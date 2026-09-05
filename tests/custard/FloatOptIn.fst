module FloatOptIn

open FStar.All

module L = FloatLib
module U32 = FStar.UInt32

(* Section 63.  The consumer side of [FloatLib], and its own opted-in type at
   the other width, so that one test covers both [float] and [double] and both
   the same-module and cross-module lookups.

   Nothing here is proved -- these are assumed vocabularies, exactly as
   [FStar.Float32] is -- so the assertion is the arithmetic itself: the
   program checks its own answers and exits nonzero if any is wrong.  That is
   what distinguishes "the attribute was read" from "the attribute was read
   and the operators came out the right way round": [sub] and [div] are not
   commutative, so an operand swap shows up here and would not show up in a
   grep for the operator. *)

[@@FStar.Attributes.custard_float 64]
assume val t : Type0

assume val add : t -> t -> t
assume val sub : t -> t -> t
assume val div : t -> t -> t
assume val lt  : t -> t -> bool
assume val lte : t -> t -> bool
assume val ieee_eq : t -> t -> bool
assume val of_literal : string -> t

let main () : ML U32.t =
  (* Width 64, declared in this module. *)
  let a = of_literal "1.5" in
  let b = of_literal "2.5" in
  let ok1 = ieee_eq (add a b) (of_literal "4.0") in
  (* Not commutative: 1.5 - 2.5 is negative, 2.5 - 1.5 is not. *)
  let ok2 = lt (sub a b) (of_literal "0.0") in
  let ok3 = lte (div a b) (of_literal "0.61") in

  (* Width 32, declared in FloatLib.  These stay single precision: written
     without the [f] suffix the literals would be doubles and the sum would be
     rounded once instead of twice. *)
  let x = L.of_literal "1.5" in
  let y = L.of_literal "2.25" in
  let ok4 = L.ieee_eq (L.add x y) (L.of_literal "3.75") in
  let ok5 = L.ieee_eq (L.mul x y) (L.of_literal "3.375") in
  (* [of_int] is a conversion and not a coercion, and at 3 there is nothing
     to round. *)
  let ok6 = L.ieee_eq (L.of_int 3L) (L.of_literal "3.0") in
  let ok7 = L.lt (L.sub x y) (L.of_literal "0.0") in

  if ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 then 0ul else 1ul
