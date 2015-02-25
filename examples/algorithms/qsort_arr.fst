module QuickSort.Seq
open Array
open Seq
open Heap
open ST
open SeqProperties
open SeqPermutation

(* (\* Defining a new predicate symbol *\) *)
(* type total_order (a:Type) (f: (a -> a -> Tot bool)) = *)
(*     (forall a. f a a)                                           (\* reflexivity   *\) *)
(*     /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (\* anti-symmetry *\) *)
(*     /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (\* transitivity  *\) *)

let splice (a:Type) (s1:seq a) (i:nat) (s2:seq a{s1.length=s2.length})  (j:nat{i <= j /\ j <= s2.length})
    = Seq.append (slice s1 0 i) (Seq.append (slice s2 i j) (slice s1 j s1.length))


assume val partition: a:Type -> f:(a -> a -> Tot bool){total_order a f} 
               -> start:nat -> len:nat{start <= len} 
               -> pivot:nat{start <= pivot /\ pivot < len} 
               -> back:nat{pivot <= back /\ back < len}
               -> x:array a -> ST nat
  (requires (fun h -> 
    contains h x 
    /\ len <= length (sel h x)
    /\ (forall (i:nat{start <= i /\ i < len}).
          ((i <= pivot ==> f (index (sel h x) i) (index (sel h x) pivot))
           /\ (back < i  ==> f (index (sel h x) pivot) (index (sel h x) i))))))
  (ensures (fun h0 i h1 -> 
    len <= length (sel h0 x)
    /\ contains h1 x
    /\ start <= i 
    /\ i < len
    /\ (length (sel h1 x) = length (sel h0 x))
    /\ (sel h1 x = splice (sel h0 x) start (sel h1 x) len)
    /\ ((fun orig lo hi p -> 
               (hi.length > 0)
            /\ (forall y. (mem y hi ==> f p y)
                       /\ (mem y lo ==> f y p)
                       /\ (count y orig = count y hi + count y lo)))
        (slice (sel h0 x) start len)
        (slice (sel h1 x) start i)
        (slice (sel h1 x) i len)
        (index (sel h1 x) i))))
  (modifies (a_ref x))


assume val lemma_slice_splice: a:Type -> s1:seq a 
         -> i:nat -> s2:seq a{length s2 = length s1} -> j:nat{i <= j /\ j <= s1.length} 
         -> k:nat{k <= i} -> Lemma
  (ensures (slice (splice s1 i s2 j) k i = slice s1 k i))

assume val lemma_splice_append: a:Type -> s1:seq a -> i:nat -> s2:seq a{s1.length = s2.length} -> j:nat{i <= j /\ j<=s1.length}
         -> k:nat{k <= i} -> Lemma 
         (ensures (slice (splice s1 i s2 j) k j = append (slice s1 k i) (slice s2 i j)))

assume val lemma_splice_append_cons: a:Type -> s1:seq a{s1.length > 0} ->  p:nat{0 < p} -> s2:seq a{s1.length = s2.length} -> j:nat{p <= j /\ j <= s1.length} -> Lemma
         (ensures (splice s2 p s1 j = append (slice s2 0 (p - 1)) (cons (index s2 (p - 1)) (slice s1 p j))))

val sort: a:Type -> f:(a -> a -> Tot bool){total_order a f} -> i:nat -> j:nat{i <= j} 
          -> x:array a -> ST unit 
  (requires (fun h -> contains h x /\ j <= length (sel h x)))
  (ensures (fun h0 u h1 -> (j <= length (sel h0 x)
                            /\ contains h1 x
                            /\ (length (sel h0 x) = length (sel h1 x))
                            /\ sorted f (slice (sel h1 x) i j)
                            /\ (sel h1 x = splice (sel h0 x) i (sel h1 x) j)
                            /\ permutation a (slice (sel h0 x) i j) (slice (sel h1 x) i j))))
  (modifies (a_ref x))
let rec sort f i j x = 
  let h0 = ST.get () in
  if i=j 
  then cut (Eq (sel h0 x) (splice (sel h0 x) i (sel h0 x) j))
  else 
    let pivot = partition f i j i (j - 1) x in
    (* assert (pivot + 1 <= j); *)

    let _h1 = ST.get () in
    let lo = slice (sel _h1 x) i pivot in
    let hi = slice (sel _h1 x) pivot j in
    let p = index (sel _h1 x) pivot in
    let hi_tl = tail hi in 
    (* assert (sel h1 x = splice (sel h0 x) i (sel h1 x) j); *)
    
    sort f i pivot x;

    let _h2 = ST.get () in    
    let l = slice (sel _h2 x) i pivot in 
    (* assert (sel _h2 x = splice (sel _h1 x) i (sel _h2 x) pivot); *)
    (* assert (sorted f l); *)
    let q = index (sel _h2 x) pivot in
    cut (b2t (p=q));


    sort f (pivot + 1) j x;

    let _h3 = ST.get () in
    let h = slice (sel _h3 x) (pivot + 1) j in
    (* assert (sel _h3 x = splice (sel _h2 x) (pivot + 1) (sel _h3 x) j); *)
    (* assert (sorted f h); *)

    lemma_slice_splice (sel _h2 x) (pivot + 1) (sel _h3 x) j i;
    assert (l=slice (sel _h3 x) i pivot);
    
    (* assert (j <= length (sel h2 x)); *)
    let r = index (sel _h3 x) pivot in
    assert (p = r);

    lemma_splice_append_cons (sel _h2 x) (pivot + 1) (sel _h3 x) j;

    assert (sel _h3 x = append l (cons p h));

    (* admit (); *)

    (* sorted_concat_lemma f l p h; *)

    (* lemma_append_count l (cons p h); *)

    (* cons_perm h hi; *)

    admit ()
       

(* val qsort: a:Type -> f:(a -> a -> Tot bool){total_order a f} -> x:array a -> ST unit  *)
(*   (requires (fun h -> contains h x)) *)
(*   (ensures (fun h0 u h1 -> sorted f (sel h1 x) /\ permutation a (sel h0 x) (sel h1 x))) *)
(*   (modifies (a_ref x)) *)
