module QuickSort.Array
open Array
open Seq
open SeqProperties
open Heap
open ST
#set-options "--initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0 --admit_smt_queries false"
type tot_ord (a:Type) = f:(a -> a -> Tot bool){total_order a f}

(* replaces the [i,j) sub-sequence of s1 with the corresponding sub-sequence of s2 *)
let splice (a:Type) (s1:seq a) (i:nat) (s2:seq a{length s1=length s2})  (j:nat{i <= j /\ j <= (length s2)})
    = Seq.append (slice s1 0 i) (Seq.append (slice s2 i j) (slice s1 j (length s1)))

opaque logic type partition_pre 
                    (a:Type) (f:tot_ord a) (start:nat) (len:nat{start <= len} )
                    (pivot:nat{start <= pivot /\ pivot < len})
                    (back:nat{pivot <= back /\ back < len})
                    (x:array a) (h:heap) = 
    (contains h x 
     /\ len <= length (sel h x)
     /\ (forall (i:nat{start <= i /\ i < len}).
         ((i <= pivot ==> f (index (sel h x) i) (index (sel h x) pivot))
     /\ (back < i  ==> f (index (sel h x) pivot) (index (sel h x) i)))))

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
    /\ ((fun orig lo hi p -> 
               ((length hi) > 0)
                /\ (forall y. (mem y hi ==> f p y)
                         /\ (mem y lo ==> f y p)
                         /\ (count y orig = count y hi + count y lo)))
        (slice (sel h0 x) start len)
        (slice (sel h1 x) start i)
        (slice (sel h1 x) i len)
        (index (sel h1 x) i)))

assume val partition: a:Type -> f:tot_ord a
               -> start:nat -> len:nat{start <= len} 
               -> pivot:nat{start <= pivot /\ pivot < len} 
               -> back:nat{pivot <= back /\ back < len}
               -> x:array a -> ST nat
  (requires (partition_pre a f start len pivot back x))
  (ensures (partition_post a f start len pivot back x))
  (modifies (a_ref x))


val lemma_seq_frame_hi: a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat{i <= j} -> m:nat{j <= m} -> n:nat{m < n && n <= length s1} 
  -> Lemma
  (requires (s1 == (splice s2 i s1 j)))
  (ensures  ((slice s1 m n == slice s2 m n) /\ (index s1 m == index s2 m)))
let lemma_seq_frame_hi s1 s2 i j m n = 
  cut (Eq (slice s1 m n) (slice s2 m n))

val lemma_seq_frame_lo: a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat{i <= j} -> m:nat{j < m} -> n:nat{m <= n && n <= length s1} 
  -> Lemma
  (requires (s1 == (splice s2 m s1 n)))
  (ensures  ((slice s1 i j == slice s2 i j) /\ (index s1 j == index s2 j)))
let lemma_seq_frame_lo s1 s2 i j m n = 
  cut (Eq (slice s1 i j) (slice s2 i j))

val lemma_tail_slice: a:Type -> s:seq a -> i:nat -> j:nat{i < j && j <= length s} 
  -> Lemma 
  (ensures (tail (slice s i j) == slice s (i + 1) j))
let lemma_tail_slice s i j = 
  cut (Eq (tail (slice s i j)) (slice s (i + 1) j))

val lemma_slice_append: a:Type -> s:seq a -> i:nat -> pivot:nat{i <= pivot} -> j:nat{pivot < j && j <= length s} -> pv:a
  -> Lemma 
  (requires (pv == index s pivot))
  (ensures (slice s i j == append (slice s i pivot) (cons pv (slice s (pivot + 1) j))))
let lemma_slice_append s i pivot j pv =
  let lo = slice s i pivot in
  let hi = slice s (pivot + 1) j in
  cut (Eq (slice s i j) (append lo (cons pv hi)))

val splice_refl : a:Type -> s:seq a -> i:nat -> j:nat 
  -> Lemma
  (ensures (s == splice s i s j))
let splice_refl s i j =
  cut (Eq s (splice s i s j))
  
val sort: a:Type -> f:tot_ord a -> i:nat -> j:nat{i <= j} -> x:array a
          -> ST unit
  (requires (fun h -> contains h x /\ j <= length (sel h x)))
  (ensures (fun h0 u h1 -> (j <= length (sel h0 x)                                      (* carrying this along from the requires clause *)
                            /\ contains h1 x                                            (* the array is still in the heap *)
                            /\ (length (sel h0 x) = length (sel h1 x))                  (* it's length has not changed *)
                            /\ sorted f (slice (sel h1 x) i j)                          (* it is sorted between [i, j) *)
                            /\ (sel h1 x == splice (sel h0 x) i (sel h1 x) j)           (* the rest of it is unchanged *)
                            /\ permutation a (slice (sel h0 x) i j) (slice (sel h1 x) i j)))) (* the [i,j) sub-array is permutation of the original one *)
  (modifies (a_ref x))
let rec sort (a:Type) f i j x =
  let h0 = ST.get () in
  if i=j
  then splie_refl (sel h0 x) i j
  else begin
               let pivot = partition f i j i (j - 1) x in
               
(* ghost *)    let h1 = get() in
(* ghost *)    let pv = index (sel h1 x) pivot in

               sort f i pivot x;

(* ghost *)    let h2 = get() in
(* ghost *)    lemma_seq_frame_hi (sel h2 x) (sel h1 x) i pivot pivot j; //slice (sel h2 x) pivot j = slice (sel h1 x) pivot j
(* ghost *)    lemma_tail_slice (sel h2 x) pivot j;

               sort f (pivot + 1) j x;

(* ghost *)    let h3 = get() in
(* ghost *)    lemma_seq_frame_lo (sel h3 x) (sel h2 x) i pivot (pivot + 1) j;
(* ghost *)    let lo = slice (sel h3 x) i pivot in
(* ghost *)    let hi = slice (sel h3 x) (pivot + 1) j in
(* ghost *)    SeqProperties.sorted_concat_lemma f lo pv hi;
(* ghost *)    lemma_slice_append (sel h3 x) i pivot j pv;

               assert (sorted f (slice (sel h3 x) i j));

               admitP ((sel h3 x)
                       ==
                      (splice (sel h0 x) i (sel h3 x) j));         (* the rest of it is unchanged *)

               admitP  (permutation a (slice (sel h0 x) i j) (slice (sel h3 x) i j))
  end
       

(* val qsort: a:Type -> f:(a -> a -> Tot bool){total_order a f} -> x:array a -> ST unit  *)
(*   (requires (fun h -> contains h x)) *)
(*   (ensures (fun h0 u h1 -> sorted f (sel h1 x) /\ permutation a (sel h0 x) (sel h1 x))) *)
(*   (modifies (a_ref x)) *)
