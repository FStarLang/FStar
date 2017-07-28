module FStar.Heap

open FStar.Preorder

include FStar.Monotonic.Heap

let trivial_preorder (a:Type0) :preorder a = fun x y -> True

type ref (a:Type0) = mref a (trivial_preorder a)
