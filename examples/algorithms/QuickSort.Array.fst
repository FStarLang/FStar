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
open FStar.Array
open FStar.Seq
open FStar.Heap
open FStar.ST
#set-options "--initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0"

(* 2016-11-22: Due to the QuickSort namespace being opened *after* the
FStar namespace,Array resolves to QuickSort.Array instead of
FStar.Array, so we have to fix this explicitly as a module abbrev. *)
module Array = FStar.Array
module Seq   = FStar.Seq

type partition_inv (a:eqtype) (f:tot_ord a) (lo:seq a) (pv:a) (hi:seq a) =
           ((length hi) >= 0)
           /\ (forall y. (mem y hi ==> f pv y) /\ (mem y lo ==> f y pv))

type partition_pre  (a:eqtype) (f:tot_ord a) (start:nat) (len:nat{start <= len} )
                    (pivot:nat{start <= pivot /\ pivot < len})
                    (back:nat{pivot <= back /\ back < len})
                    (x:array a) (h:heap) =
    (Array.contains h x
     /\ ((let s = Array.sel h x in (len <= length s) /\ (partition_inv a f
                                                       (slice s start pivot)
                                                       (index s pivot)
                                                       (slice s (back + 1) len)))
           ))

type partition_post (a:eqtype) (f:tot_ord a) (start:nat) (len:nat{start <= len} )
                    (pivot:nat{start <= pivot /\ pivot < len})
                    (back:nat{pivot <= back /\ back < len})
                    (x:array a) (h0:heap) (i:nat) (h1:heap) =
   (len <= length (Array.sel h0 x)
    /\ Array.contains h1 x
    /\ start <= i
    /\ i < len
    /\ (length (Array.sel h1 x) = length (Array.sel h0 x))
    /\ (Array.sel h1 x == splice (Array.sel h0 x) start (Array.sel h1 x) len)
    /\ (permutation a (slice (Array.sel h0 x) start len) (slice (Array.sel h1 x) start len))
    /\ (partition_inv a f
                      (slice (Array.sel h1 x) start i)
                      (index (Array.sel h1 x) i)
                      (slice (Array.sel h1 x) i len)))

#reset-options "--z3rlimit 20 --initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0"
val partition: #a:eqtype -> f:tot_ord a
               -> start:nat -> len:nat{start <= len}
               -> pivot:nat{start <= pivot /\ pivot < len}
               -> back:nat{pivot <= back /\ back < len}
               -> x:array a -> ST nat
  (requires (partition_pre a f start len pivot back x))
  (ensures (fun h0 n h1 -> partition_post a f start len pivot back x h0 n h1 /\ modifies (Array.only x) h0 h1))
let rec partition #a f start len pivot back x =
  let h0 = get() in
  if pivot = back
  then
    begin
(*ghost*)      (let s = Array.sel h0 x in
(*ghost*)       lemma_slice_cons s pivot len;
(*ghost*)       splice_refl s start len);
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
          let h1 = get () in
	  let _ =
(* ghost *)           let s = Array.sel h0 x in
(* ghost *)           let s' = Array.sel h1 x in
(* ghost *)           swap_frame_lo s start pivot (pivot + 1);
(* ghost *)           swap_frame_hi s pivot (pivot + 1) (back + 1) len;
                      assume (pivot < length s');
                      //lemma_swap_splice s start (pivot + 1) back len;
                      (* need pivot < length s',
                         but only have pivot < length s *)
(* ghost *)           lemma_ordering_lo_snoc f s' start pivot p in
          let res = partition f start len (pivot + 1) back x in
	  let h2 = get () in
          let _ =
(* ghost *)           let s = Array.sel h0 x in
(* ghost *)           let s' = Array.sel h1 x in
(* ghost *)           let s'' = Array.sel h2 x in
(* ghost *)           lemma_swap_splice s start pivot (pivot + 1) len;
(* ghost *)           lemma_trans_frame s'' s' s start len;
(* ghost *)           lemma_swap_permutes_slice s start pivot (pivot + 1) len;
(* ghost *)           lemma_trans_perm s s' s'' start len in
          res
        end
      else
        begin
          Array.swap x (pivot + 1) back; (* the back moves backward *)
	  let h1 = get () in
// (* ghost *)           let s = Array.sel h0 x in
// (* ghost *)           let s' = Array.sel h1 x in
// (* ghost *)           swap_frame_lo' s start pivot (pivot + 1) back;
// (* ghost *)           swap_frame_hi s (pivot + 1) back (back + 1) len;
// (* ghost *)           lemma_ordering_hi_cons f s' back len p in
          let res = partition f start len pivot (back - 1) x in
	  let h2 = get () in
	  let _ =
(* ghost *)           let s = Array.sel h0 x in
(* ghost *)           let s' = Array.sel h1 x in
(* ghost *)           let s'' = Array.sel h2 x in
(* ghost *)           lemma_swap_splice s start (pivot + 1) back len;
(* ghost *)           lemma_trans_frame s'' s' s start len;
(* ghost *)           lemma_swap_permutes_slice s start (pivot + 1) back len;
(* ghost *)           lemma_trans_perm s s' s'' start len in
          res
        end
    end
#reset-options

val lemma_slice_cons_pv: #a:Type -> s:seq a -> i:nat -> pivot:nat{i <= pivot} -> j:nat{pivot < j && j <= length s} -> pv:a
  -> Lemma
  (requires (pv == index s pivot))
  (ensures (slice s i j == append (slice s i pivot) (cons pv (slice s (pivot + 1) j))))
let lemma_slice_cons_pv #a s i pivot j pv =
  let lo = slice s i pivot in
  let hi = slice s (pivot + 1) j in
  cut (Seq.equal (slice s i j) (append lo (cons pv hi)))

#reset-options
#set-options "--initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0 --z3rlimit 50"
val sort: #a:eqtype -> f:tot_ord a -> i:nat -> j:nat{i <= j} -> x:array a
          -> ST unit
  (requires (fun h -> Array.contains h x /\ j <= length (Array.sel h x)))
  (ensures (fun h0 u h1 -> (modifies (Array.only x) h0 h1
                            /\ j <= length (Array.sel h0 x)                                      (* carrying this along from the requires clause *)
                            /\ Array.contains h1 x                                            (* the array is still in the heap *)
                            /\ (length (Array.sel h0 x) = length (Array.sel h1 x))                  (* its length has not changed *)
                            /\ sorted f (slice (Array.sel h1 x) i j)                          (* it is sorted between [i, j) *)
                            /\ (Array.sel h1 x == splice (Array.sel h0 x) i (Array.sel h1 x) j)           (* the rest of it is unchanged *)
                            /\ permutation a (slice (Array.sel h0 x) i j) (slice (Array.sel h1 x) i j)))) (* the [i,j) sub-array is a permutation of the original one *)
let rec sort #a f i j x =
  let h0 = ST.get () in
  if i=j
  then splice_refl (Array.sel h0 x) i j
  else begin
               let pivot = partition f i j i (j - 1) x in

(* ghost *)    let h1 = get() in

               sort f i pivot x;

(* ghost *)    let h2 = get() in
	       let _ =
(* ghost *)      lemma_seq_frame_hi (Array.sel h2 x) (Array.sel h1 x) i pivot pivot j;
(* ghost *)      lemma_tail_slice (Array.sel h2 x) pivot j in

               sort f (pivot + 1) j x;

(* ghost *)    let h3 = get() in
(* ghost *)    lemma_seq_frame_lo (Array.sel h3 x) (Array.sel h2 x) i pivot (pivot + 1) j;
(* ghost *)    let lo = slice (Array.sel h3 x) i pivot in
(* ghost *)    let hi = slice (Array.sel h3 x) (pivot + 1) j in
(* ghost *)    let pv = index (Array.sel h1 x) pivot in
(* ghost *)    Seq.sorted_concat_lemma f lo pv hi;
(* ghost *)    lemma_slice_cons_pv (Array.sel h3 x) i pivot j pv;

(* ghost *)    lemma_weaken_frame_right (Array.sel h2 x) (Array.sel h1 x) i pivot j;
(* ghost *)    lemma_weaken_frame_left (Array.sel h3 x) (Array.sel h2 x) i (pivot + 1) j;
(* ghost *)    lemma_trans_frame (Array.sel h3 x) (Array.sel h2 x) (Array.sel h1 x) i j;
(* ghost *)    lemma_trans_frame (Array.sel h3 x) (Array.sel h1 x) (Array.sel h0 x) i j;

(* ghost *)    lemma_weaken_perm_right (Array.sel h2 x) (Array.sel h1 x) i pivot j;
(* ghost *)    lemma_weaken_perm_left (Array.sel h3 x) (Array.sel h2 x) i (pivot + 1) j
  end


val qsort: #a:eqtype -> f:tot_ord a -> x:array a -> ST unit
  (requires (fun h -> Array.contains h x))
  (ensures (fun h0 u h1 -> modifies (Array.only x) h0 h1
                        /\ Array.contains h1 x /\ sorted f (Array.sel h1 x) /\ permutation a (Array.sel h0 x) (Array.sel h1 x)))
let qsort #a f x =
  let h0 = get() in

  let len = Array.length x in
  sort f 0 len x;

  let h1 = get() in
  cut (Seq.equal (Array.sel h0 x) (slice (Array.sel h0 x) 0 len));
  cut (Seq.equal (Array.sel h1 x) (slice (Array.sel h1 x) 0 len))
