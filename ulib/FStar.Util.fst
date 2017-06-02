module FStar.Util

open FStar.Heap
open FStar.HyperHeap

(* 2016-11-22: the following MUST be defined here AFTER the above `open',
   since they are used in [op_At_Plus_At] below *)
let op_Plus_Plus x y = TSet.union x y
let op_Plus_Plus_Hat x y = x ++ (TSet.singleton y)
let op_Hat_Plus_Hat  x y = (TSet.singleton x) ++ (TSet.singleton y)

let op_At_Plus_At (#a:Type) (#r:rid) (#b:Type) (#s:rid) (x:rref r a) (y:rref s b) =
   Set.union (Set.singleton (Heap.addr_of (as_ref x))) (Set.singleton (Heap.addr_of (as_ref y)))
let op_Plus_Plus_At (#a:Type) (#r:rid) (x:Set.set nat) (y:rref r a) = Set.union x (Set.singleton (Heap.addr_of (as_ref y)))
