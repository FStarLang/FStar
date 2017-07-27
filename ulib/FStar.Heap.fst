module FStar.Heap

include FStar.Monotonic.Heap

type ref (a:Type0) = mref a (Preorder.trivial_preorder a)
