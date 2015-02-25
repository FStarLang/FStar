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
            /\ (forall x. (mem x hi ==> f p x)
            /\ (mem x lo ==> f x p)
            /\ (count x orig = count x hi + count x lo)))
        (slice (sel h0 x) start len)
        (slice (sel h1 x) start i)
        (slice (sel h1 x) i len)
        (index (sel h1 x) i))))
  (modifies (a_ref x))

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
    let h1 = ST.get () in
    sort f i pivot x;
    let h2 = ST.get () in
    sort f (pivot + 1) j x;
    let h3 = ST.get () in
    assert (sel h1 x = splice (sel h0 x) i (sel h1 x) j);
    assert (sorted f (slice (sel h2 x) i pivot));
    assert (sorted f (slice (sel h3 x) (pivot + 1) j));
    (* assert (Eq (slice (sel h3 x) i j) *)
    (*            (append (slice (sel h2 x) i pivot) *)
    (*                    (cons (index (sel h1 x) pivot) *)
    (*                          (slice (sel h3 x) (pivot + 1) j)))); *)
    admit ()
       

(* val qsort: a:Type -> f:(a -> a -> Tot bool){total_order a f} -> x:array a -> ST unit  *)
(*   (requires (fun h -> contains h x)) *)
(*   (ensures (fun h0 u h1 -> sorted f (sel h1 x) /\ permutation a (sel h0 x) (sel h1 x))) *)
(*   (modifies (a_ref x)) *)
