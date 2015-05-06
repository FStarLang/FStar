(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module QuickSort.Array
open Array
open Seq
open SeqProperties
open Heap
open ST
#set-options "--initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0"

opaque type partition_inv (a:Type) (f:tot_ord a) (lo:seq a) (pv:a) (hi:seq a) =
           ((length hi) >= 0)
           /\ (forall y. (mem y hi ==> f pv y) /\ (mem y lo ==> f y pv))

opaque logic type partition_pre
                    (a:Type) (f:tot_ord a) (start:nat) (len:nat{start <= len} )
                    (pivot:nat{start <= pivot /\ pivot < len})
                    (back:nat{pivot <= back /\ back < len})
                    (x:array a) (h:heap) =
    (contains h x
     /\ ((fun s -> (len <= length s) /\ (partition_inv a f
                                                       (slice s start pivot)
                                                       (index s pivot)
                                                       (slice s (back + 1) len)))
           (sel h x)))

opaque logic type partition_post
                    (a:Type) (f:tot_ord a) (start:nat) (len:nat{start <= len} )
                    (pivot:nat{start <= pivot /\ pivot < len})
                    (back:nat{pivot <= back /\ back < len})
                    (x:array a) (h0:heap) (i:nat) (h1:heap) =
   (len <= length (sel h0 x)
    /\ contains h1 x
    /\ start <= i
    /\ i < len
    /\ (length (sel h1 x) = length (sel h0 x))
    /\ (sel h1 x = splice (sel h0 x) start (sel h1 x) len)
    /\ (permutation a (slice (sel h0 x) start len) (slice (sel h1 x) start len))
    /\ (partition_inv a f
                      (slice (sel h1 x) start i)
                      (index (sel h1 x) i)
                      (slice (sel h1 x) i len)))

#reset-options
#set-options "--initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0"
val partition: #a:Type -> f:tot_ord a
               -> start:nat -> len:nat{start <= len}
               -> pivot:nat{start <= pivot /\ pivot < len}
               -> back:nat{pivot <= back /\ back < len}
               -> x:array a -> ST nat
  (requires (partition_pre a f start len pivot back x))
  (ensures (partition_post a f start len pivot back x))
  (modifies (a_ref x))
let rec partition (a:Type) f start len pivot back x =
  let h0 = get() in
  let s = sel h0 x in
  if pivot = back
  then
    begin
      lemma_slice_cons s pivot len;
      splice_refl s start len;
      pivot
    end
  else
    begin
      let next = Array.index x (pivot + 1) in
      let p = Array.index x pivot in
      if f next p
      then
        begin
          Array.swap x pivot (pivot + 1);  (* the pivot moves forward *)
(* ghost *)           let h1 = get () in
(* ghost *)           let s' = sel h1 x in
(* ghost *)           swap_frame_lo s start pivot (pivot + 1);
(* ghost *)           swap_frame_hi s pivot (pivot + 1) (back + 1) len;
(* ghost *)           lemma_ordering_lo_snoc f s' start pivot p;
          let res = partition f start len (pivot + 1) back x in
(* ghost *)           let h2 = get () in
(* ghost *)           let s'' = sel h2 x in
(* ghost *)           lemma_swap_splice s start pivot (pivot + 1) len;
(* ghost *)           lemma_trans_frame s'' s' s start len;
(* ghost *)           lemma_swap_permutes_slice s start pivot (pivot + 1) len;
(* ghost *)           lemma_trans_perm s s' s'' start len;
          res
        end
      else
        begin
          Array.swap x (pivot + 1) back; (* the back moves backward *)

(* ghost *)          let h1 = get () in
(* ghost *)          let s' = sel h1 x in
(* ghost *)          swap_frame_lo' s start pivot (pivot + 1) back;
(* ghost *)          swap_frame_hi s (pivot + 1) back (back + 1) len;
(* ghost *)          lemma_ordering_hi_cons f s' back len p;
          let res = partition f start len pivot (back - 1) x in
(* ghost *)          let h2 = get () in
(* ghost *)          let s'' = sel h2 x in
(* ghost *)          lemma_swap_splice s start (pivot + 1) back len;
(* ghost *)          lemma_trans_frame s'' s' s start len;
(* ghost *)          lemma_swap_permutes_slice s start (pivot + 1) back len;
(* ghost *)          lemma_trans_perm s s' s'' start len;
          res
        end
    end


val lemma_slice_cons_pv: #a:Type -> s:seq a -> i:nat -> pivot:nat{i <= pivot} -> j:nat{pivot < j && j <= length s} -> pv:a
  -> Lemma
  (requires (pv == index s pivot))
  (ensures (slice s i j == append (slice s i pivot) (cons pv (slice s (pivot + 1) j))))
let lemma_slice_cons_pv s i pivot j pv =
  let lo = slice s i pivot in
  let hi = slice s (pivot + 1) j in
  cut (Eq (slice s i j) (append lo (cons pv hi)))

#reset-options
#set-options "--initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0"
val sort: #a:Type -> f:tot_ord a -> i:nat -> j:nat{i <= j} -> x:array a
          -> ST unit
  (requires (fun h -> contains h x /\ j <= length (sel h x)))
  (ensures (fun h0 u h1 -> (j <= length (sel h0 x)                                      (* carrying this along from the requires clause *)
                            /\ contains h1 x                                            (* the array is still in the heap *)
                            /\ (length (sel h0 x) = length (sel h1 x))                  (* its length has not changed *)
                            /\ sorted f (slice (sel h1 x) i j)                          (* it is sorted between [i, j) *)
                            /\ (sel h1 x == splice (sel h0 x) i (sel h1 x) j)           (* the rest of it is unchanged *)
                            /\ permutation a (slice (sel h0 x) i j) (slice (sel h1 x) i j)))) (* the [i,j) sub-array is a permutation of the original one *)
  (modifies (a_ref x))
let rec sort (a:Type) f i j x =
  let h0 = ST.get () in
  if i=j
  then splice_refl (sel h0 x) i j
  else begin
               let pivot = partition f i j i (j - 1) x in

(* ghost *)    let h1 = get() in
(* ghost *)    let pv = index (sel h1 x) pivot in

               sort f i pivot x;

(* ghost *)    let h2 = get() in
(* ghost *)    lemma_seq_frame_hi (sel h2 x) (sel h1 x) i pivot pivot j;
(* ghost *)    lemma_tail_slice (sel h2 x) pivot j;

               sort f (pivot + 1) j x;

(* ghost *)    let h3 = get() in
(* ghost *)    lemma_seq_frame_lo (sel h3 x) (sel h2 x) i pivot (pivot + 1) j;
(* ghost *)    let lo = slice (sel h3 x) i pivot in
(* ghost *)    let hi = slice (sel h3 x) (pivot + 1) j in
(* ghost *)    SeqProperties.sorted_concat_lemma f lo pv hi;
(* ghost *)    lemma_slice_cons_pv (sel h3 x) i pivot j pv;

(* ghost *)    lemma_weaken_frame_right (sel h2 x) (sel h1 x) i pivot j;
(* ghost *)    lemma_weaken_frame_left (sel h3 x) (sel h2 x) i (pivot + 1) j;
(* ghost *)    lemma_trans_frame (sel h3 x) (sel h2 x) (sel h1 x) i j;
(* ghost *)    lemma_trans_frame (sel h3 x) (sel h1 x) (sel h0 x) i j;

(* ghost *)    lemma_weaken_perm_right (sel h2 x) (sel h1 x) i pivot j;
(* ghost *)    lemma_weaken_perm_left (sel h3 x) (sel h2 x) i (pivot + 1) j
  end


val qsort: #a:Type -> f:tot_ord a -> x:array a -> ST unit
  (requires (fun h -> contains h x))
  (ensures (fun h0 u h1 -> contains h1 x /\ sorted f (sel h1 x) /\ permutation a (sel h0 x) (sel h1 x)))
  (modifies (a_ref x))
let qsort f x =
  let h0 = get() in

  let len = Array.length x in
  sort f 0 len x;

  let h1 = get() in
  cut (Eq (sel h0 x) (slice (sel h0 x) 0 len));
  cut (Eq (sel h1 x) (slice (sel h1 x) 0 len))
