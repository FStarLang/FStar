(* Expect 5 intentional failures *)
module TestSet
assume type elt
assume logic val A : elt
assume logic val B : elt
assume logic val C : elt
assume AB_distinct: A=!=B
open Set

val should_succeed: unit -> Tot unit
let should_succeed u =
  assert (mem B (union (singleton A) (singleton B)));
  assert (mem A (union (singleton A) (singleton B)));
  assert (Subset (singleton A) (union (singleton A) (singleton B)));
  assert (Subset (singleton B) (union (singleton A) (singleton B)));
  assert (Equal (union (singleton A) (singleton B))
                (union (singleton B) (singleton A)))


module TestHeap
open Set
open Heap
assume val x : ref int
assume val y : ref int
assume val h : heap
assume DistinctXY: x <> y

let test0 _ = assert (sel (upd h x 0) x = 0)
let test1 _ = assert (sel (upd (upd h x 0) y 1) x = 0)
let test3 _ = assert (sel (upd (upd h x 0) y 1) y = 1)
let h1 = upd (upd h x 0) y 1
let test5 _ = assert (equal h1 (upd (upd h y 1) x 0))

val ys: set aref (* required *)
let ys = Set.singleton (Ref y)

let test6 _ = assert (equal h1 (concat h1 (restrict h1 (complement ys))))
let test7 _ = assert (contains h1 x)
let test8 _ = assert (contains h y ==> contains (upd h x 0) y)
let test9 (x:ref int) =
  assume (not (contains h x));
  assert (equal (upd h x 0) (concat (upd h x 0) (restrict h (complement empty))))
