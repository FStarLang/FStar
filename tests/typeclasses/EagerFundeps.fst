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

(* The pointer may be a data constructor application whose type arguments
   are still uvars when the value is checked: [Cell r i : cell ?a ?i]. They
   are pinned to the types of [r] and [i], keeping the refinement of [nat]. *)
noeq type cell a i = | Cell : a -> i -> cell a i

instance has_pts_to_cell (x : Type) : has_pts_to (cell (ref x) nat) x = {
  pts_to = (fun c x -> True);
}

let test6 (r : ref int) (i : nat) (y : erased int) : GTot prop = pts_to (Cell r i) y

(* The pointer's type may also be refined, with uvars under the refinement:
   [mk_cell r i : c:cell ?a ?i{True}]. As for a uvar bounded by a ground
   type, the refinement is dropped at the top. *)
assume val mk_cell (#a #i : Type) (x : a) (y : i) : c:cell a i{True}

let test7 (r : ref int) (i : nat) (y : erased int) : GTot prop = pts_to (mk_cell r i) y

(* A nested uvar is pinned to its bound, refinement included, so an instance
   at a supertype of the index is not found: [i : nat] fixes [cell _ nat]. *)
noeq type cell2 a i = | Cell2 : a -> i -> cell2 a i

instance has_pts_to_cell2 (x : Type) : has_pts_to (cell2 (ref x) int) x = {
  pts_to = (fun c x -> True);
}

[@@expect_failure [228]]
let test8 (r : ref int) (i : nat) (y : erased int) : GTot prop = pts_to (Cell2 r i) y

(* Ascribing the index works. *)
let test9 (r : ref int) (i : nat) (y : erased int) : GTot prop = pts_to (Cell2 r (i <: int)) y

(* The pointer may be an application of a polymorphic function: the type
   [?c] of [myid x] is bounded by the type argument [?a] of [myid], which in
   turn is bounded by [ref int]. The chain of bounds is followed. *)
let myid (#a : Type) (x : a) : a = x
type pos = x:int{x > 0}
let test10 (x : ref int) (y : pos) = pts_to (myid x) y
let test11 (x : ref int) (y : erased int) : GTot prop = pts_to (myid x) y
