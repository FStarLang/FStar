module FStar.Heap

open FStar.Preorder

include FStar.Monotonic.Heap

let trivial_preorder' (a:Type0) :relation a = fun x y -> True
let trivial_preorder (a:Type0)  :preorder a = trivial_preorder' a

type ref (a:Type0) = mref a (trivial_preorder a)
