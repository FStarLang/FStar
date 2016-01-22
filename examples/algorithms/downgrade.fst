(*--build-config
  options:--z3timeout 20;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Set.fst FStar.Heap.fst
              stperm.fst seq.fsi FStar.Seq.fst FStar.SeqProperties.fst FStar.Array.fst
              qs_seq.fst qsort_arr.fst
--*)
module Downgrade
#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"
open FStar.Array
open FStar.Seq
open FStar.SeqProperties
open FStar.ST
open FStar.Heap
type tot_ord (a:Type) = f:(a -> a -> Tot bool){total_order a f}

val qsort_seq : #a:Type -> f:tot_ord a -> x:seq a -> ST (seq a)
   (fun h -> True)
   (fun h0 y h1 -> modifies !{} h0 h1 /\ sorted f y /\ permutation a x y)
let qsort_seq f x =
  let x_ar = Array.of_seq x in
  QuickSort.Array.qsort f x_ar;
  let res = to_seq x_ar in
  free x_ar;
  res

val qsort_seq_forget: #a:Type -> f:tot_ord a -> s1:seq a -> Dv (s2:seq a{sorted f s2 /\ permutation a s1 s2})
let qsort_seq_forget f x =
  //forget_ST (qsort_seq f) x <-- this doesn't work because of a bug
  let g = forget_ST (qsort_seq f) in
  g x
