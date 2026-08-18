module OvlUserCoercion
open OvlMeters
open OvlInt
open OvlBool
open OvlMetersB
open OvlMetersA

(* A [@@coercion]-annotated function widens the set of types the elaborator
   will silently convert between, so it has to widen the set of types overload
   resolution is willing to call compatible by exactly as much. Otherwise a
   candidate that only typechecks because of a user coercion is eliminated
   before the coercion is ever considered, and nothing recovers from that.

   Overload.compatible therefore reads the coercions out of the environment
   with the same function Util.find_coercion uses to select them. *)

(* By argument type. OvlBool is opened after OvlInt, so [f] is OvlBool.f by
   scope order. Neither candidate takes a [meters]; OvlInt.f is the one whose
   argument a [meters] can be coerced to, and it is the answer. *)
let use_arg (m:meters) : int = f m

(* By expected type. OvlMetersA is opened last, so [pick] is OvlMetersA.pick by
   scope order. Both candidates take an [int], so only the result discriminates,
   and it does so only because [int] coerces to [meters]. *)
let use_expected (x:int) : meters = pick x
