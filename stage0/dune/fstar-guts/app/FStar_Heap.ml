open FStar_Monotonic_Heap

type 'a ref = 'a FStar_Monotonic_Heap.ref
type ('a, 'b, 'c) trivial_rel = Prims.l_True
type ('a, 'b, 'c) trivial_preorder = ('a, 'b, 'c) trivial_rel
