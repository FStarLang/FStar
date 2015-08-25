(*--build-config
    options:--admit_fsi Heap --admit_fsi Heap --admit_fsi HyperHeap;
    other-files:ext.fst set.fsi heap.fst map.fsi hyperheap2.fsi
  --*)
module FStar.Util

let op_Plus_Plus x y = Set.union x y
let op_Plus_Plus_Hat x y = x ++ (Set.singleton y)
let op_Hat_Plus_Hat  x y = (Set.singleton x) ++ (Set.singleton y)

open FStar.Heap
open Fstar.HyperHeap
let op_At_Plus_At (#a:Type) (#r:rid) (#b:Type) (#s:rid) (x:rref r a) (y:rref s b) =
   Ref (as_ref x) ^+^ Ref (as_ref y)
let op_Plus_Plus_At (#a:Type) (#r:rid) (x:Set.set aref) (y:rref r a) = x ++^ Ref (as_ref y)
