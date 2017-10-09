module FStar.HyperStack

include FStar.Monotonic.HyperStack

open FStar.Monotonic.HyperHeap

type reference (a:Type) = mreference a (Preorder.trivial_preorder a)

let stackref (a:Type) = mstackref a (Preorder.trivial_preorder a)
let ref (a:Type) = mref a (Preorder.trivial_preorder a)

let mmstackref (a:Type) = mmmstackref a (Heap.trivial_preorder a)
let mmref (a:Type) = mmmref a (Heap.trivial_preorder a)
type s_ref (i:rid) (a:Type) = s_mref i a (Heap.trivial_preorder a)
