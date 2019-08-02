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
module QuickSort.Seq
open FStar.Seq

(* 2016-11-22: Due to the QuickSort namespace being opened *after* the
FStar namespace, Seq resolves to QuickSort.Seq instead of FStar.Seq,
so we have to fix this explicitly as a module abbrev. *)
module Seq = FStar.Seq

#reset-options "--z3rlimit 100 --max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val partition: #a:eqtype -> f:(a -> a -> Tot bool){total_order a f}
    -> s:seq a -> pivot:nat{pivot < length s} -> back:nat{pivot <= back /\ back < length s} ->
       Pure (seq a * seq a)
         (requires (forall (i:nat{i < length s}).
                                 ((i <= pivot ==> f (index s i) (index s pivot))
                                  /\ (back < i  ==> f (index s pivot) (index s i)))))
         (ensures (fun res ->
                     (fun lo hi p ->
                         (length lo + length hi = length s)
                      /\ (length hi > 0)
                      /\ (index hi 0 = p)
                      /\ (forall x. (mem x hi ==> f p x)
                                 /\ (mem x lo ==> f x p)
                                 /\ (count x s = count x hi + count x lo)))
                     (fst res)
                     (snd res)
                     (index s pivot)))
         (decreases (back - pivot))
let rec partition #a f s pivot back =
  if pivot=back
  then (lemma_count_slice s pivot;
        let lo = slice s 0 pivot in
        let hi = slice s pivot (length s) in
        lemma_mem_count lo (fun x -> f x (index s pivot));
        lemma_mem_count hi (f (index s pivot));
        (lo, hi))
  else let next = index s (pivot + 1) in
       let p = index s pivot in
       if f next p
       then let s' = swap s pivot (pivot + 1) in  (* the pivot moves forward *)
            let _ = lemma_swap_permutes s pivot (pivot + 1) in
            partition f s' (pivot + 1) back
       else let s' = swap s (pivot + 1) back in (* the back moves backward *)
            let _ = lemma_swap_permutes s (pivot + 1) back in
            let res = (* admit() *) partition f s' pivot (back - 1) in
            res        

#reset-options

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
val sort: #a:eqtype -> f:(a -> a -> Tot bool){total_order a f}
       -> s1:seq a
       -> Tot (s2:seq a{sorted f s2 /\ permutation a s1 s2})
              (decreases (length s1))
let rec sort #a f s =
  if length s <= 1 then s
  else let lo, hi = partition f s 0 (length s - 1) in
       let pivot = head hi in

       let hi_tl = tail hi in
       let l = sort f lo in
       let h = sort f hi_tl in

       let result = Seq.append l (cons pivot h) in

       sorted_concat_lemma f l pivot h;
       lemma_append_count l (cons pivot h);
       cons_perm h hi;

       result



