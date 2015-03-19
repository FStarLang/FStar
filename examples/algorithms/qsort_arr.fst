module QuickSort.Array
open Array
open Seq
open SeqProperties
open Heap
open ST
#set-options "--initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0 --admit_smt_queries false"

(* replaces the [i,j) sub-sequence of s1 with the corresponding sub-sequence of s2 *)
let splice (a:Type) (s1:seq a) (i:nat) (s2:seq a{length s1=length s2})  (j:nat{i <= j /\ j <= (length s2)})
    = Seq.append (slice s1 0 i) (Seq.append (slice s2 i j) (slice s1 j (length s1)))

val splice_refl : a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s}
  -> Lemma
  (ensures (s == splice s i s j))
let splice_refl s i j = cut (Eq s (splice s i s j))

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

assume val lemma_slice_cons: a:Type -> s:seq a -> i:nat -> j:nat{i < j && j <= length s} 
  -> Lemma (ensures (forall x. mem x (slice s i j) <==> (x = index s i || mem x (slice s (i + 1) j))))

assume val lemma_slice_snoc: a:Type -> s:seq a -> i:nat -> j:nat{i < j && j <= length s} 
  -> Lemma (ensures (forall x. mem x (slice s i j) <==> (x = index s (j - 1) || mem x (slice s i (j - 1)))))

assume val swap_frame_lo : a:Type -> s:seq a -> lo:nat -> i:nat{lo <= i} -> j:nat{i <= j && j < length s} 
     -> Lemma (ensures (slice s lo i == slice (swap s i j) lo i))                                                     

assume val swap_frame_lo' : a:Type -> s:seq a -> lo:nat -> i':nat {lo <= i'} -> i:nat{i' <= i} -> j:nat{i <= j && j < length s} 
     -> Lemma (ensures (slice s lo i' == slice (swap s i j) lo i'))                                                     

assume val swap_frame_hi : a:Type -> s:seq a -> i:nat -> j:nat{i <= j} -> k:nat{j < k} -> hi:nat{k <= hi /\ hi <= length s}
     -> Lemma (ensures (slice s k hi == slice (swap s i j) k hi))                                                         

assume val lemma_partition_inv_lo_snoc: a:Type -> f:tot_ord a -> s:seq a -> i:nat -> j:nat{i <= j && j < length s} -> pv:a
   -> Lemma (requires ((forall y. mem y (slice s i j) ==> f y pv) /\ f (index s j) pv))
            (ensures ((forall y. mem y (slice s i (j + 1)) ==> f y pv)))

val lemma_swap_splice : a:Type -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
   -> Lemma 
        (ensures (swap s i j == splice s start (swap s i j) len))
let lemma_swap_splice s start i j len = cut (Eq (swap s i j) (splice s start (swap s i j) len))

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

  
val lemma_weaken_frame_right : a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j && j <= k && k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 i s1 j))
  (ensures (s1 == splice s2 i s1 k))
let lemma_weaken_frame_right s1 s2 i j k = cut (Eq s1 (splice s2 i s1 k))

val lemma_weaken_frame_left : a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j && j <= k && k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 j s1 k))
  (ensures (s1 == splice s2 i s1 k))
let lemma_weaken_frame_left s1 s2 i j k = cut (Eq s1 (splice s2 i s1 k))

val lemma_trans_frame : a:Type -> s1:seq a -> s2:seq a -> s3:seq a{length s1 = length s2 /\ length s2 = length s3} -> i:nat -> j:nat{i <= j && j <= length s1}
  -> Lemma
  (requires ((s1 == splice s2 i s1 j) /\ s2 == splice s3 i s2 j))
  (ensures (s1 == splice s3 i s1 j))
let lemma_trans_frame s1 s2 s3 i j = cut (Eq s1 (splice s3 i s1 j))

val lemma_weaken_perm_left: a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j /\ j <= k /\ k <= length s1} 
  -> Lemma
  (requires (s1 == splice s2 j s1 k /\ permutation a (slice s2 j k) (slice s1 j k)))
  (ensures (permutation a (slice s2 i k) (slice s1 i k)))
let lemma_weaken_perm_left s1 s2 i j k = 
  cut (Eq (slice s2 i k) (append (slice s2 i j) 
                                 (slice s2 j k)));
  cut (Eq (slice s1 i k) (append (slice s2 i j)
                                 (slice s1 j k)));
  lemma_append_count (slice s2 i j) (slice s2 j k);
  lemma_append_count (slice s2 i j) (slice s1 j k)
 
val lemma_weaken_perm_right: a:Type -> s1:seq a -> s2:seq a{length s1 = length s2} -> i:nat -> j:nat -> k:nat{i <= j /\ j <= k /\ k <= length s1}
  -> Lemma
  (requires (s1 == splice s2 i s1 j /\ permutation a (slice s2 i j) (slice s1 i j)))
  (ensures (permutation a (slice s2 i k) (slice s1 i k)))
let lemma_weaken_perm_right s1 s2 i j k = 
  cut (Eq (slice s2 i k) (append (slice s2 i j) 
                                 (slice s2 j k)));
  cut (Eq (slice s1 i k) (append (slice s1 i j)
                                 (slice s2 j k)));
  lemma_append_count (slice s2 i j) (slice s2 j k);
  lemma_append_count (slice s1 i j) (slice s2 j k)

val lemma_trans_perm: a:Type -> s1:seq a -> s2:seq a -> s3:seq a{length s1 = length s2 /\ length s2 = length s3} -> i:nat -> j:nat{i<=j && j <= length s1}
 -> Lemma 
  (requires (permutation a (slice s1 i j) (slice s2 i j)
             /\ permutation a (slice s2 i j) (slice s3 i j)))
  (ensures (permutation a (slice s1 i j) (slice s3 i j)))
let lemma_trans_perm s1 s2 s3 i j = ()

assume val lemma_partition_inv_hi_cons: a:Type -> f:tot_ord a -> s:seq a -> back:nat -> len:nat{back < len && len <= length s} -> pv:a
   -> Lemma (requires ((forall y. mem y (slice s (back + 1) len) ==> f pv y) /\ f pv (index s back)))
            (ensures ((forall y. mem y (slice s back len) ==> f pv y)))

assume val lemma_swap_permutes_slice : a:Type -> s:seq a -> start:nat -> i:nat{start <= i} -> j:nat{i <= j} -> len:nat{j < len && len <= length s}
   -> Lemma (ensures (permutation a (slice s start len) (slice (SeqProperties.swap s i j) start len)))

val swap: a:Type -> x:array a -> i:nat -> j:nat{i <= j} 
                 -> St unit (requires (fun h -> contains h x /\ j < length (sel h x)))
                            (ensures (fun h0 _u h1 -> 
                                      (j < length (sel h0 x))
                                      /\ contains h1 x
                                      /\ (h1==upd h0 x (SeqProperties.swap (sel h0 x) i j))))
                            (* (modifies (a_ref x)) *)
let swap x i j =
  let h0 = get () in
  let s0 = sel h0 x in
  let tmpi = Array.index x i in
  let tmpj = Array.index x j in
  Array.upd x j tmpi;
  Array.upd x i tmpj;
  let h1 = get () in
  let s1 = sel h1 x in
  cut (b2t(equal h1 (upd h0 x s1)))


#reset-options
#set-options "--initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0 --admit_smt_queries false"                                                                                                            
val partition: a:Type -> f:tot_ord a
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
          swap x pivot (pivot + 1);  (* the pivot moves forward *)
(* ghost *)           let h1 = get () in
(* ghost *)           let s' = sel h1 x in
(* ghost *)           swap_frame_lo s start pivot (pivot + 1);
(* ghost *)           swap_frame_hi s pivot (pivot + 1) (back + 1) len;
(* ghost *)           lemma_partition_inv_lo_snoc f s' start pivot p;
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
          swap x (pivot + 1) back; (* the back moves backward *)
          
(* ghost *)          let h1 = get () in
(* ghost *)          let s' = sel h1 x in
(* ghost *)          swap_frame_lo' s start pivot (pivot + 1) back; 
(* ghost *)          swap_frame_hi s (pivot + 1) back (back + 1) len;
(* ghost *)          lemma_partition_inv_hi_cons f s' back len p;
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


#reset-options
#set-options "--initial_fuel 1 --initial_ifuel 0 --max_fuel 1 --max_ifuel 0 --admit_smt_queries false"
val sort: a:Type -> f:tot_ord a -> i:nat -> j:nat{i <= j} -> x:array a
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
(* ghost *)    lemma_slice_append (sel h3 x) i pivot j pv;

(* ghost *)    lemma_weaken_frame_right (sel h2 x) (sel h1 x) i pivot j;
(* ghost *)    lemma_weaken_frame_left (sel h3 x) (sel h2 x) i (pivot + 1) j;
(* ghost *)    lemma_trans_frame (sel h3 x) (sel h2 x) (sel h1 x) i j;
(* ghost *)    lemma_trans_frame (sel h3 x) (sel h1 x) (sel h0 x) i j;

(* ghost *)    lemma_weaken_perm_right (sel h2 x) (sel h1 x) i pivot j;
(* ghost *)    lemma_weaken_perm_left (sel h3 x) (sel h2 x) i (pivot + 1) j
  end
       

val qsort: a:Type -> f:tot_ord a -> x:array a -> ST unit
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

