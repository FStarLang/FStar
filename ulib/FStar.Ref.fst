module FStar.Ref

(* wrapper over FStar.ST to provide operations over refs with default preorder *)

include FStar.Heap
include FStar.ST

open FStar.Heap
open FStar.ST

abstract let sel (#a:Type0) (h:heap) (r:ref a) :GTot (x:a{x == Heap.sel h r})
  = Heap.sel h r

abstract let upd (#a:Type0) (h:heap) (r:ref a) (v:a) :GTot (h1:heap{h1 == Heap.upd h r v})
  = Heap.upd h r v

abstract let addr_of (#a:Type0) (r:ref a) :GTot (n:nat{n == Heap.addr_of r}) = addr_of r

abstract let contains (#a:Type0) (h:heap) (r:ref a) :GTot (p:Type0{p <==> Heap.contains h r})
  = Heap.contains h r

abstract let unused_in (#a:Type0) (r:ref a) (h:heap) :GTot (p:Type0{p <==> Heap.unused_in r h})
  = Heap.unused_in r h

abstract let fresh (#a:Type0) (r:ref a) (h0:heap) (h1:heap) :GTot (p:Type0{p <==> Heap.fresh r h0 h1})
  = Heap.fresh r h0 h1

abstract let only (#a:Type0) (r:ref a) :GTot (s:Set.set nat{s == Heap.only r})
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
