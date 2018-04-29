module FStar.Heap

include FStar.Monotonic.Heap

let trivial_rel (a: Type0) : Preorder.relation a = fun x y -> True

let trivial_preorder (a: Type0) : Preorder.preorder a = trivial_rel a

type ref (a: Type0) = mref a (trivial_preorder a)

