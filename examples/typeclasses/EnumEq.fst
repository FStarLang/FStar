module EnumEq

open Enum
open Eq
open FStar.Tactics.Typeclasses

(* Trying out a "class morphism", a post-facto relation between two existing classes. *)
[@instance]
let enum_eq (#a:Type) (d : enum a) : deq a = {
    (* Why the #d annotation? A tricky dependency causes the meta-arg
     * annotation to vanish. First we solve that the type where this
     * comparison occurs is (Enum.bounded (Mkenum?.max #a ?u)), then
     * we solve both of the dictionaries here with ?u. So they *ARE*
     * solved, and the meta-arg annotation is lost. What should happen,
     * is that when we solve a meta-implicit with a uvar, the meta-annotation
     * should be copied. (But what about the environment?) *)
    eq    = (fun (x y : a) -> toInt #_ #d x = toInt y);
    eq_ok = (fun (x y : a) -> inv1 x; inv1 y);
}

let test #a [|enum a|] (x y : a) : bool =
  eq x y
