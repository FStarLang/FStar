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

val sort: a:Type -> f:tot_ord a -> i:nat -> j:nat{i <= j} -> x:array a 
          -> ST unit 
  (requires (fun h -> contains h x /\ j <= length (sel h x)))
  (ensures (fun h0 u h1 -> (j <= length (sel h0 x)                                      (* carrying this along from the requires clause *)
                            /\ contains h1 x                                            (* the array is still in the heap *)
                            /\ (length (sel h0 x) = length (sel h1 x))                  (* it's length has not changed *)
                            /\ sorted f (slice (sel h1 x) i j)                          (* it is sorted between [i, j) *)
                            /\ Eq (sel h1 x) (splice (sel h0 x) i (sel h1 x) j)         (* the rest of it is unchanged *)
                            /\ permutation a (slice (sel h0 x) i j) (slice (sel h1 x) i j)))) (* the [i,j) sub-array is permutation of the original one *)
  (modifies (a_ref x))
let rec sort (a:Type) f i j x = 
  let h0 = ST.get () in
  if i=j 
  then ()
  else begin
      let h0 = get() in
      let pivot = partition f i j i (j - 1) x in
      
      
      let h1 = get() in
      let pv = index (sel h1 x) pivot in


      sort f i pivot x;
      let h2 = get() in

      admitP ((slice (sel h2 x) pivot j) 
                 == 
              (slice (sel h1 x) pivot j));

      admitP ((tail (slice (sel h2 x) pivot j)) 
                 ==
              (slice (sel h2 x) (pivot + 1) j));

      admitP (forall y. mem y (slice (sel h2 x) (pivot + 1) j) ==> f pv y);


      sort f (pivot + 1) j x;
      let h3 = get() in

      admitP ((slice (sel h3 x) i pivot)
                 ==
              (slice (sel h2 x) i pivot));

      
      admitP (forall y. mem y (slice (sel h3 x) i pivot) ==> f y pv);

      admitP (forall y. mem y (slice (sel h3 x) (pivot + 1) j) ==> f pv y);


      let lo = slice (sel h3 x) i pivot in
      let hi = slice (sel h3 x) (pivot + 1) j in

      (* cut (sorted f lo); *)
      (* cut (sorted f hi); *)

      (* cut (forall y. mem y lo ==> f y pv); *)

      (* cut (forall y. mem y (slice (sel h3 x) pivot j) ==> f pv y); *)
      SeqProperties.sorted_concat_lemma f lo pv hi;

      admitP ((slice (sel h3 x) i j)
                 ==
              (append lo (cons pv hi)));
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
