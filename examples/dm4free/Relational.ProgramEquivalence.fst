module Relational.ProgramEquivalence

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

reifiable let f () :STNull unit =
  let r = alloc_weak 0 in
  ()

let f_obs (h0:heap) =
  let _, h1 = reify (f ()) h0 in
  assert (forall (a:Type) (r:ref a). h0 `contains_a_well_typed` r ==> sel h0 r == sel h1 r)
