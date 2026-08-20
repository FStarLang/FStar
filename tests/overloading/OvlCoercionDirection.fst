module OvlCoercionDirection
open OvlInt
open OvlBool
open OvlFeet

(* A [@@coercion] relates two types in one direction only, and overload
   resolution has to respect that direction. Taking the relation
   symmetrically keeps candidates that the elaborator could never make
   sense of, and since resolution is final, the occurrence then fails to
   typecheck against a candidate that was never applicable. See #4455. *)

(* 1. The bug. [OvlFeet] is opened last, so [( * )] is [OvlFeet.( * )] by
   scope order. Its formals are [feet], and while a [feet] coerces to an
   [int], an [int] does not coerce to a [feet]: the [int] arguments here
   cannot reach it, so the answer is [Prims.op_Star]. *)
let mul_int (x y : int) : int = x * y

(* 2. Same site, [feet] arguments. Both candidates survive the arguments,
   since [feet] does coerce to the [int] that [Prims.op_Star] expects; the
   expected type is what settles it, and it settles it by direction too --
   an [int] result cannot become the [feet] that is expected. *)
let mul_feet (x y : feet) : feet = x * y

(* 3. The coercion still applies where it points. [OvlBool.f] takes a
   [bool] and [OvlInt.f] an [int], and only the latter can receive a
   [feet]. *)
let arg_coerced (x:feet) : int = f x

(* 4. Likewise on results: [OvlInt.mk] returns [OvlInt.t] and
   [OvlFeet.mk] a [feet], and only a [feet] can become the expected
   [int]. *)
let result_coerced (x:int) : int = mk x

(* 5. The report, verbatim: [FStar.SizeT] is opened over [Prims] and the
   coercion goes from [FStar.SizeT.t] to [int], so multiplying two [int]s
   is [Prims.op_Star] and not [FStar.SizeT.op_Star]. *)
module SizeT = FStar.SizeT
open FStar.SizeT

[@@coercion]
let sizet_to_int (x: SizeT.t) : GTot int = SizeT.v x

let mul_sizet_scope (x y : int) : int = x * y
