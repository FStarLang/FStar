module EnumEq

open Enum
open Eq
open FStar.Tactics.Typeclasses

(* Trying out a "class morphism", a post-facto relation between two existing classes. *)
instance enum_eq (#a:Type) (d : enum a) : deq a = {
    eq    = (fun (x y : a) -> toInt x = toInt y);
    eq_ok = (fun (x y : a) -> inv1 x; inv1 y);
}

let test #a [|enum a|] (x y : a) : bool =
  eq x y
