open Prims
open FStar_DM4F_Heap
open FStar_DM4F_Heap_ST

type inductive_inv = heap -> Obj.t

type (_,_,_,_,_,_,_,_) invariant = unit

let erase_st: type a b wp. (a -> (b, wp) _dm4f_STATE_repr) -> a -> b =
  fun f ->
  let r = ref emp in
  fun x -> let y, h = f x !r in r := h ; y
