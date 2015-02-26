module Downgrade
open Array
open Seq
open SeqProperties
open SeqPermutation
open ST
open Heap

assume val qsort_arr: a:Type -> f:(a -> a -> Tot bool){total_order a f} -> x:array a -> ST unit
  (requires (fun h -> contains h x))
  (ensures (fun h0 u h1 -> contains h1 x /\ sorted f (sel h1 x) /\ permutation a (sel h0 x) (sel h1 x)))
  (modifies (a_ref x))

type tot_ord (a:Type) = f:(a -> a -> Tot bool){total_order a f}

val qsort_seq : a:Type -> f:tot_ord a -> x:seq a -> ST (seq a)
  (requires (fun h -> True))
  (ensures (fun h0 y h1 -> sorted f y /\ permutation a x y))
  (modifies (no_refs))
let qsort_seq f x =
  let x_ar = Array.of_seq x in
  qsort_arr f x_ar;
  let res = to_seq x_ar in 
  free x_ar;
  res

assume val down: a:Type -> b:(a -> Type) -> req:(a -> heap -> Type) -> ens:(x:a -> heap -> b x -> heap -> Type) 
         -> =f:(x:a -> ST (b x) (req x) (ens x) no_refs){(forall (x:a) (h:heap). req x h)}
         -> Tot (x:a -> Div (b x) True (fun (y:b x) -> exists h0 h1. ens x h0 y h1))

val qsort_seq_down: a:Type -> f:tot_ord a -> s1:seq a -> Dv (s2:seq a{sorted f s2 /\ permutation a s1 s2})
let qsort_seq_down f x = down (qsort_seq f)  x

