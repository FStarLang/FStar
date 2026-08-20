module OvlMeters
(* A type related to [int] by user coercions in both directions. Used by
   OvlUserCoercion to check that overload resolution sees them. *)

type meters = | Meters of int

[@@coercion]
let meters_to_int (m:meters) : int = Meters?._0 m

[@@coercion]
let int_to_meters (x:int) : meters = Meters x
