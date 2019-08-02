(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Downgrade
#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"
open FStar.Array
open FStar.Seq
open FStar.ST
open FStar.Heap
type tot_ord (a:Type) = f:(a -> a -> Tot bool){total_order a f}

val qsort_seq : #a:Type -> f:tot_ord a -> x:seq a -> ST (seq a)
   (fun h -> True)
   (fun h0 y h1 -> modifies !{} h0 h1 /\ sorted f y /\ permutation a x y)
let qsort_seq #a f x =
  let x_ar = Array.of_seq x in
  QuickSort.Array.qsort f x_ar;
  let res = to_seq x_ar in
  free x_ar;
  res

val qsort_seq_forget: #a:Type -> f:tot_ord a -> s1:seq a -> Dv (s2:seq a{sorted f s2 /\ permutation a s1 s2})
let qsort_seq_forget #a f x =
  //forget_ST (qsort_seq f) x <-- this doesn't work because of a bug
  let g = forget_ST (qsort_seq f) in
  g x
