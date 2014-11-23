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
  assert (equal (union (singleton A) (singleton B))
                (union (singleton B) (singleton A)))

val should_fail1: unit -> Tot unit
let should_fail1 u =
  assert (mem B (singleton A))

val should_fail2: unit -> Tot unit
let should_fail2 u = 
  assert (Subset (union (singleton A) (singleton B)) (singleton A))

val should_fail3: unit -> Tot unit
let should_fail3 u =
  assert (mem C (union (singleton A) (singleton B)))
            

module TestHeap
open Set
open Heap
assume val x : ref int
assume val y : ref int
assume val h : heap
assume DistinctXY: x <> y

let test0 _ = assert (sel (upd h x 0) x = 0)
let test1 _ = assert (sel (upd (upd h x 0) y 1) x = 0)
let test2 _ = assert (sel (upd (upd h x 0) y 1) y = 0) //should fail
let test3 _ = assert (sel (upd (upd h x 0) y 1) y = 1)
let h1 = upd (upd h x 0) y 1
let test5 _ = assert (equal h1 (upd (upd h y 1) x 0))
let ys = Set.singleton (Ref y)
let test6 _ = assert (equal h1 (concat h1 (restrict h1 (complement ys))))
let test7 _ = assert (contains h1 x)
let test8 _ = assert (contains h y ==> contains (upd h x 0) y)
let test9 (x:ref int) =
  assume (not (contains h x));
  assert (equal (upd h x 0) (concat (upd h x 0) (restrict h (complement empty))))
let test10 (x:ref int) (y:ref int) (h0:heap) (h1:heap) (h2:heap) =
  admitP (h1 == concat h1 (restrict h0 (complement empty))) ();
  admitP (h1 == upd h0 x 0) ();
  admitP (~ (contains h1 y)) ();
  assert false //should fail
