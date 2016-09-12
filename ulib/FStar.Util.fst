module FStar.Util

let op_Plus_Plus x y = TSet.union x y
let op_Plus_Plus_Hat x y = x ++ (TSet.singleton y)
let op_Hat_Plus_Hat  x y = (TSet.singleton x) ++ (TSet.singleton y)

open FStar.Heap
open FStar.HyperHeap
let op_At_Plus_At (#a:Type) (#r:rid) (#b:Type) (#s:rid) (x:rref r a) (y:rref s b) =
   Set.union (Set.singleton (Heap.addr_of (as_ref x))) (Set.singleton (Heap.addr_of (as_ref y)))
let op_Plus_Plus_At (#a:Type) (#r:rid) (x:Set.set nat) (y:rref r a) = Set.union x (Set.singleton (Heap.addr_of (as_ref y)))
