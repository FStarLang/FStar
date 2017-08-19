open Prims
open FStar_DM4F_Heap
open FStar_DM4F_Heap_ST

type inductive_inv = heap -> Obj.t

type (_,_,_,_,_,_,_,_) invariant = unit

type ('a,_) erase_initializer = unit -> ('a, Obj.t) _dm4f_STATE_repr

let erase_st: type a b r inv wp. (r -> a -> (b, wp) _dm4f_STATE_repr) -> (r, inv) erase_initializer -> a -> b =
  fun f init ->
  let r0, h0 = init () emp in
  let r = ref h0 in
  let f' = f r0 in
  fun x -> let y, h = f' x !r in r := h ; y
