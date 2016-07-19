(* ******************************************************************************** *)
module NegativeTests.Heap
open FStar.TSet
open FStar.Heap
assume val x : ref int
assume val y : ref int
assume val h : heap
assume DistinctXY: x =!= y

let test2 _ = assert (sel (upd (upd h x 0) y 1) y = 0) //should fail
let test10 (x:ref int) (y:ref int) (h0:heap) (h1:heap) (h2:heap) =
  admitP (h1 == concat h1 (restrict h0 (complement empty)));
  admitP (h1 == upd h0 x 0);
  admitP (~ (contains h1 y));
  assert false //should fail
