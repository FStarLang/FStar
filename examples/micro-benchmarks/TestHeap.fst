module TestHeap
open FStar.TSet
open FStar.Heap
assume val x : ref int
assume val y : ref int
assume val h : h:heap{h `contains` x /\ h `contains` y}
assume DistinctXY: addr_of x =!= addr_of y

let test0 _ = assert (sel (upd h x 0) x = 0)
let test1 _ = assert (sel (upd (upd h x 0) y 1) x = 0)
let test3 _ = assert (sel (upd (upd h x 0) y 1) y = 1)

(* we don't have heap equality *)
(* let test5 _ =  *)
(*   let h1 = upd (upd h x 0) y 1 in *)
(*   assert (equal h1 (upd (upd h y 1) x 0)) *)

//let ys = singleton (Ref y)

(* let test6 _ =  *)
(*   let h1 = upd (upd h x 0) y 1 in *)
(*   assert (equal h1 (concat h1 (restrict h1 (complement ys)))) *)
let test7 _ = 
  let h1 = upd (upd h x 0) y 1 in
  assert (contains h1 x)
let test8 _ = assert (contains h y ==> contains (upd h x 0) y)
(* let test9 (x:ref int) = *)
(*   assume (not (contains h x)); *)
(*   assert (equal (upd h x 0) (concat (upd h x 0) (restrict h (complement empty)))) *)
