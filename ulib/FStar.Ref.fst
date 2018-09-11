module FStar.Ref

(* wrapper over FStar.ST to provide operations over refs with default preorder *)

include FStar.Heap
include FStar.ST

open FStar.Heap
open FStar.ST

unfold
let sel (#a:Type0) (h:heap) (r:ref a) : GTot a
  = Heap.sel h r

unfold
let upd (#a:Type0) (h:heap) (r:ref a) (v:a) :GTot heap
  = Heap.upd h r v

unfold
let addr_of (#a:Type0) (r:ref a) : GTot nat = addr_of r

unfold
let contains (#a:Type0) (h:heap) (r:ref a) :GTot Type0
  = Heap.contains h r

unfold
let unused_in (#a:Type0) (r:ref a) (h:heap) :GTot Type0
  = Heap.unused_in r h

unfold
let fresh (#a:Type0) (r:ref a) (h0:heap) (h1:heap) : Type0
  = Heap.fresh r h0 h1

unfold
let only (#a:Type0) (r:ref a) :GTot (Set.set nat)
  = Heap.only r

abstract let recall (#a:Type0) (r:ref a)
  :STATE unit (fun p h -> h `contains` r ==> p () h)
  = recall r

abstract let alloc (#a:Type0) (init:a)
  :ST (ref a)
      (fun _       -> True)
      (fun h0 r h1 -> fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init)
  = alloc init

abstract let read (#a:Type0) (r:ref a) :STATE a (fun p h -> p (sel h r) h)
  = read r

abstract let write (#a:Type0) (r:ref a) (v:a)
  :ST unit (fun _ -> True) (fun h0 _ h1 -> h0 `contains` r /\ modifies (only r) h0 h1 /\ equal_dom h0 h1 /\ sel h1 r == v)
  = write r v

abstract let op_Bang (#a:Type0) (r:ref a) :STATE a (fun p h -> p (sel h r) h)
  = read r

abstract let op_Colon_Equals (#a:Type0) (r:ref a) (v:a)
  :ST unit (fun _ -> True) (fun h0 _ h1 -> h0 `contains` r /\ modifies (only r) h0 h1 /\ equal_dom h0 h1 /\ sel h1 r == v)
  = write r v
