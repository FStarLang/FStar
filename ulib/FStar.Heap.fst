module FStar.Heap

include FStar.Monotonic.Heap

let trivial_preorder (a:Type0) = fun x y -> True

type ref (a:Type0) = mref a (trivial_preorder a)
