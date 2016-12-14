module TestHeapST

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

(* reifiable let x () : STNull unit = () *)

(* let chose (h0 : heap) (r:(ref int)) (_:unit{h0 `contains_a_well_typed` r}) = *)
(*   let h1 = normalize_term (snd (reify (write r 42) h0)) in *)
(*   assert (h1 == upd h0 r 42) *)


let truc (h0 : heap) (r:(ref int)) (_:unit{h0 `contains_a_well_typed` r}) =
  let h = normalize_term (snd (reify (let x = read r in write r x) h0)) in
  assert_norm (h == upd h0 r (sel h0 r))
