module EagerFundeps

open FStar.Tactics.Typeclasses
open FStar.Ghost

[@@fundeps [1]]
class has_pts_to (p x : Type) = {
  pts_to : p -> x -> prop;
}

assume val ref : Type0 -> Type0

instance has_pts_to_ref (x : Type) : has_pts_to (ref x) x = {
  pts_to = (fun r x -> True);
}

(* This has to fail, but it has to fail *quickly*. *)
[@@expect_failure [228]]
let test (x:int) y = pts_to x y

let test1 (x : ref int) = pts_to x 2

(* The fundep is resolved from [x] before [y] is checked, so [y] is checked
   against [int] and [reveal] is inserted. No instance for [erased] needed. *)
let test2 (x : ref int) (y : erased int) : GTot prop = pts_to x y
let _ = assert (forall (x : ref int) (y : erased int). test2 x y == pts_to x (reveal y))

(* Likewise, refinements of the value type are accepted by subtyping. *)
let test3 (x : ref int) (y : nat) = pts_to x y

(* With nothing known about [y], the fundep determines its type. *)
let test4 (x : ref int) = exists y. pts_to x y
let test5 (x : ref int) = exists y. pts_to x y /\ y == 3
