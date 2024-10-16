module FStar_Heap

open FStar_Monotonic_Heap

type 'a ref = 'a FStar_Monotonic_Heap.ref
type trivial_rel = Prims.l_True
type trivial_preorder = trivial_rel
