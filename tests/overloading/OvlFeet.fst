module OvlFeet
(* A type related to [int] by a coercion in *one* direction only: a
   [feet] can be turned into an [int], but not the other way around.
   Contrast with OvlMeters, which supplies both directions. *)

type feet = | Feet of int

[@@coercion]
let feet_to_int (x:feet) : int = Feet?._0 x

(* Overloads of names that Prims and OvlInt also provide. *)
let ( * ) (x y : feet) : feet = Feet (feet_to_int x * feet_to_int y)
let mk (x:int) : feet = Feet x
