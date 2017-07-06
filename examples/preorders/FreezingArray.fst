module FreezingArray

open FStar.Preorder
open FStar.Heap
open FStar.ST

module Set = FStar.Set

open FStar.Seq

(***** some sequence properties *****)

let init_at_seq (#a:Type0) (s:seq (option a)) (i:nat{i < length s}) :Type0
  = Some? (index s i)

let all_some (#a:Type0) (s:seq (option a)) :Type0
  = forall (i:nat). i < length s ==> Some? (index s i)

(*
 * a sequence of option a is equivalent to a sequence of a, if all are Some and contained values match
 *)
let some_equivalent_seqs (#a:Type0) (s1:Seq.seq (option a)) (s2:Seq.seq a) :Type0
  = (Seq.length s1 == Seq.length s2) /\
    (forall (i:nat). i < Seq.length s1 ==> Some (Seq.index s2 i) == Seq.index s1 i)

(* assuming this function, quite straightforward, just strip out the Some *)
assume val get_some_equivalent (#a:Type0) (s:Seq.seq (option a))
  : Pure (seq a)
         (requires (all_some s))
	 (ensures  (fun r -> some_equivalent_seqs s r))

assume val lemma_get_some_equivalent_length (#a:Type0) (s:seq (option a))
  :Lemma (requires (all_some s))
         (ensures  (all_some s /\
	            length (get_some_equivalent s) == length s))
	 [SMTPat (length (get_some_equivalent s))]

assume val lemma_get_some_equivalent_index (#a:Type0) (s:seq (option a)) (i:nat)
  :Lemma (requires (all_some s /\ i < length s))
         (ensures  (all_some s /\ i < length s /\
	            Some? (index s i) /\ Some (index (get_some_equivalent s) i) == index s i))
	 [SMTPat (index (get_some_equivalent s) i)]

assume val lemma_get_some_equivalent_snoc (#a:Type0) (s:seq (option a)) (x:option a)
  :Lemma (requires (all_some s /\ Some? x))
         (ensures  (all_some s /\ Some? x /\
	            get_some_equivalent (snoc s x) == snoc (get_some_equivalent s) (Some?.v x)))
	 [SMTPatOr [[SMTPat (get_some_equivalent (snoc s x))]; [SMTPat (snoc (get_some_equivalent s) (Some?.v x))]]]

assume val lemma_get_some_equivalent_append (#a:Type0) (s1:seq (option a)) (s2:seq (option a))
  :Lemma (requires (all_some s1 /\ all_some s2))
         (ensures  (all_some s1 /\ all_some s2 /\
	            get_some_equivalent (append s1 s2) == append (get_some_equivalent s1) (get_some_equivalent s2)))
	 [SMTPatOr [[SMTPat (get_some_equivalent (append s1 s2))]; [SMTPat (append (get_some_equivalent s1) (get_some_equivalent s2))]]]

assume val lemma_get_some_equivalent_slice (#a:Type0) (s:seq (option a)) (i:nat) (j:nat)
  :Lemma (requires (all_some s /\ j >= i /\ j < Seq.length s))
         (ensures  (all_some s /\ j >= i /\ j < Seq.length s /\
	            get_some_equivalent (slice s i j) == slice (get_some_equivalent s) i j))

	 [SMTPatOr [[SMTPat (get_some_equivalent (slice s i j))]; [SMTPat (slice (get_some_equivalent s) i j)]]]

let lemma_get_equivalent_sequence_slice
  (#a:Type0) (s:seq (option a)) (i:nat) (j:nat)
  (s':seq a)
  :Lemma (requires (j >= i /\ j <= Seq.length s /\
                    Seq.length s' = j - i    /\
		    (forall (k:nat). (k >= i /\ k < j) ==> Seq.index s k == Some (Seq.index s' (k - i)))))
         (ensures  (j >= i /\ j <= Seq.length s /\
                    Seq.length s' = j - i    /\
		    (forall (k:nat). (k >= i /\ k < j) ==> Seq.index s k == Some (Seq.index s' (k - i))) /\
	            get_some_equivalent (Seq.slice s i j) == s'))
  = admit ()

assume val copy_seq (#a:Type0) (s1:seq (option a)) (i:nat) (j:nat) (s2:seq a)
  :Pure (seq (option a))
        (requires (j >= i /\ j <= Seq.length s1 /\ Seq.length s2 = j - i))
	(ensures  (fun r -> j >= i /\ j <= Seq.length s1 /\ Seq.length s2 = j - i /\
	                 Seq.length r == Seq.length s1                      /\
                         (forall (k:nat).
			    (k < i ==> (Seq.index r k == Seq.index s1 k)) /\
			    ((k >= i /\ k < j) ==> (Seq.index r k == Some (Seq.index s2 (k - i)))) /\
		            ((k >= j /\ k < Seq.length s1) ==> (Seq.index r k == Seq.index s1 k)))))

(*****)

private type flag =
  | Mutable
  | MutableUntilFrozen
  | Frozen

(*
 * representation of an array, a sequence of options and a flag, with an invariant that
 * if the flag is Frozen, the sequence is all Some
 *)
private type repr (a:Type0) (n:nat) :Type0 =
  t:(Seq.seq (option a) * flag){Seq.length (fst t) = n /\ ((snd t == Frozen) ==> all_some (fst t))}

(*
 * relation (preorder) between sequences
 * if b1 is set, b2 is also set, and the sequences remain same (frozen)
 * in any case, once a sequence entry is Some, it remains Some
 *)
private type seq_rel (a:Type0) (n:nat) :relation (repr a n)
  = fun (t1:repr a n) (t2:repr a n) -> let s1, f1 = t1 in
                                    let s2, f2 = t2 in
				    (f1 == Mutable ==> f2 == Mutable)               /\
				    (f1 == Frozen ==> f2 == Frozen)                 /\
				    (f1 == MutableUntilFrozen ==> (f2 =!= Mutable)) /\
				    (f1 == Frozen  ==> s1 == s2)                    /\  //once the seq is frozen, it remains so
				    (forall (i:nat). i < n ==> (init_at_seq s1 i ==> init_at_seq s2 i))  //once an index is init, it remains so

(* typing the relation above as preorder *)
private let seq_pre (a:Type0) (n:nat) :preorder (repr a n) = seq_rel a n

(*
 * an array is a mref and an offset into the array (for taking interior pointers)
 * the view of an array is from offset to m
 *)
noeq abstract type t (a:Type0) (n:nat) =
  | A: #m:nat -> s_ref:mref (repr a m) (seq_pre a m) -> offset:nat{offset + n <= m} -> t a n

abstract type mutable_pred' (#a:Type0) (#n:nat) (x:t a n) :heap_predicate
  = fun h ->
    let A #_ #_ #_ s_ref _ = x in
    h `Heap.contains` s_ref /\ (snd (sel h s_ref) == Mutable)

abstract type mutable_pred (#a:Type0) (#n:nat) (x:t a n) :(p:heap_predicate{stable p})
  = mutable_pred' x

abstract type freezable_pred' (#a:Type0) (#n:nat) (x:t a n) :heap_predicate
  = fun h ->
    let A #_ #_ #_ s_ref _ = x in
    h `Heap.contains` s_ref /\ (snd (sel h s_ref) == MutableUntilFrozen \/ (snd (sel h s_ref) == Frozen))

abstract type freezable_pred (#a:Type0) (#n:nat) (x:t a n) :(p:heap_predicate{stable p})
  = freezable_pred' x

type farray (a:Type0) (n:nat) = x:t a n{witnessed (freezable_pred x)}  //an array that you intend to freeze in future

type array (a:Type0) (n:nat) = x:t a n{witnessed (mutable_pred x)}  //an array that you don't intend to freeze

(*
 * this is true if the current array has full view of the underlying array
 * we currently require freezing only on the full array
 *)
abstract let is_full_array (#a:Type0) (#n:nat) (arr:t a n) :bool =
  let A #_ #_ #m _ off = arr in
  off = 0 && n = m

(*
 * footprint of the array in the heap
 *)
abstract let array_footprint (#a:Type0) (#n:nat) (arr:t a n) :GTot (Set.set nat)
  = let A s_ref _ = arr in
    Set.singleton (addr_of s_ref)

(*
 * liveness of an array in the heap
 *)
abstract let contains_array (#a:Type) (#n:nat) (h:heap) (arr:t a n)
  = let A #_ #_ #_ s_ref _ = arr in
    h `Heap.contains` s_ref

(*
 * this is a precondition for writing, essentially, it will be false once you freeze the array
 *)
abstract let is_mutable (#a:Type0) (#n:nat) (arr:t a n) (h:heap)
  = let A #_ s_ref _ = arr in
    let f = snd (sel h s_ref) in
    f == Mutable \/ f == MutableUntilFrozen

let fresh_arr (#a:Type0) (#n:nat) (arr:t a n) (h0 h1:heap)
  = h1 `contains_array` arr /\  //array is live in h1
    (forall (n:nat). Set.mem n (array_footprint arr) ==> n `addr_unused_in` h0)  //the footprint of array was unused in h0, hopefully this enables the clients to maintain separation

(*
 * create an array that you intend to freeze some time in future
 *)
abstract let fcreate (a:Type0) (n:nat)
  :ST (farray a n) (requires (fun _         -> True))
                   (ensures  (fun h0 arr h1 -> fresh_arr arr h0 h1      /\  //it's fresh
		                            modifies Set.empty h0 h1 /\  //no existing refs are changed
					    is_mutable arr h1        /\  //the array is mutable
					    is_full_array arr))         //and has the full view of the underlying sequence
  = let arr = A #a #n #n (alloc ((Seq.create n None), MutableUntilFrozen)) 0 in
    gst_witness (freezable_pred arr);
    arr

(*
 * create an array, that always remains mutable
 *)
abstract let create (a:Type0) (n:nat)
  :ST (array a n) (requires (fun _         -> True))
                  (ensures  (fun h0 arr h1 -> fresh_arr arr h0 h1      /\  //it's fresh
		                           modifies Set.empty h0 h1 /\  //no existing refs are changed
					   is_full_array arr))         //and has the full view of the underlying sequence
  = let arr = A #a #n #n (alloc ((Seq.create n None), Mutable)) 0 in
    gst_witness (mutable_pred arr);
    arr

(*
 * type of a valid index into an array
 *)
type index (#a:Type0) (#n:nat) (arr:t a n) = i:nat{i < n}

(*
 * Ghost view of an array as a sequence of options
 *)
abstract let as_seq (#a:Type0) (#n:nat) (arr:t a n) (h:heap)
  :GTot (s:Seq.seq (option a))
  = let A #_ #_ #_ s_ref off = arr in
    let s = fst (sel h s_ref) in
    Seq.slice s off (off + n)

let lemma_as_seq_length (#a:Type0) (#n:nat) (arr:t a n) (h:heap)
  :Lemma (requires True)
         (ensures  (Seq.length (as_seq arr h) = n))
	 [SMTPat (Seq.length (as_seq arr h))]
  = ()

(* scaffolding for init_at *)
abstract let init_at_arr (#a:Type0) (#n:nat) (arr:t a n) (i:index arr) (h:heap) :Type0
  = let s = as_seq arr h in
    init_at_seq s i

private let init_at_pred' (#a:Type0) (#n:nat) (arr:t a n) (i:index arr) :heap_predicate
  = fun h -> h `contains_array` arr /\ init_at_arr arr i h

(* a stable init_at predicate *)
abstract let init_at_pred (#a:Type0) (#n:nat) (arr:t a n) (i:index arr) :(p:heap_predicate{stable p})
  = let A #_ #_ #m s_ref off = arr in
    assert (forall (h:heap).
              let s, _ = sel h s_ref in
	      init_at_arr arr i h <==> Some? (Seq.index s (off + i)));
    assert (forall (h1 h2:heap).
              let s1, _ = sel h1 s_ref in
	      let s2, _ = sel h2 s_ref in
              (h1 `contains_array` arr /\ heap_rel h1 h2) ==> (forall (i:nat). i < m ==> (Some? (Seq.index s1 i) ==>
	                                                                          Some? (Seq.index s2 i))));
    init_at_pred' arr i

(* witnessed predicate for init_at *)
abstract let init_at (#a:Type0) (#n:nat) (arr:t a n) (i:index arr) :Type0
  = witnessed (init_at_pred arr i)

(* scaffolding for frozen predicate *)
abstract let frozen_bit (#a:Type0) (#n:nat) (arr:t a n) (h:heap) :Type0
  = let A s_ref _ = arr in
    snd (sel h s_ref) == Frozen

private type frozen_pred' (#a:Type0) (#n:nat) (arr:t a n) (s:Seq.seq a) :heap_predicate
  = fun h -> h `contains_array` arr /\ some_equivalent_seqs (as_seq arr h) s /\ frozen_bit arr h

open FStar.Ghost

(* a stable frozen predicate *)
abstract type frozen_pred (#a:Type0) (#n:nat) (arr:t a n) (s:erased (Seq.seq a)) :(p:heap_predicate{stable p})
  = frozen_pred' arr (reveal s)

(* witnessed predicate for frozen *)
abstract type frozen_with (#a:Type0) (#n:nat) (arr:t a n) (s:erased (Seq.seq a)) :Type0
  = Seq.length (reveal s) == n /\ witnessed (frozen_pred arr s)

(***** serious stuff starts now *****)

(*
 * freeze an array
 *)
abstract let freeze (#a:Type0) (#n:nat) (arr:farray a n)
  :ST (s:erased (Seq.seq a))
      (requires (fun h0       -> is_full_array arr /\  //can only freeze full arrays
                              (forall (i:nat). i < n ==> init_at_arr arr i h0)))  //all elements must be init_at
      (ensures  (fun h0 es h1 -> some_equivalent_seqs (as_seq arr h0) (reveal es) /\  //the returned ghost sequence is the current view of array in the heap
                              frozen_with arr es                          /\  //witnessing the stable predicate
                              (~ (is_mutable arr h1))                     /\  //the array is no longer mutable
			      modifies (array_footprint arr) h0 h1))  //only array footprint is changed
  = gst_recall (freezable_pred arr);
    let A #_ s_ref _ = arr in
    let s, b = !s_ref in
    s_ref := (s, Frozen);
    gst_witness (frozen_pred arr (hide (get_some_equivalent s)));
    hide (get_some_equivalent s)

(*
 * read from an array
 *)
abstract let read (#a:Type0) (#n:nat) (arr:t a n) (i:index arr{arr `init_at` i})  //the index must be `init_at`
  :ST a (requires (fun h0      -> True))
        (ensures  (fun h0 r h1 -> h0 == h1 /\ Some r == Seq.index (as_seq arr h0) i))
  = let A #_ s_ref o = arr in
    let (s, _) = !s_ref in
    gst_recall (init_at_pred arr i);
    Some?.v (Seq.index s (o + i))

private let write_common (#a:Type0) (#n:nat) (arr:t a n) (i:nat{i < n}) (x:a)
  :ST unit (requires (fun h0       -> is_mutable arr h0))  //the array must be mutable
           (ensures  (fun h0 () h1 -> modifies (array_footprint arr) h0 h1 /\  //only array is modified
	                           is_mutable arr h1                    /\  //the array remains mutable
				   arr `init_at` i                      /\  //witness the stable init predicate
				   Seq.index (as_seq arr h1) i == Some x))  //update the ghost view of the array
  = let A #_ s_ref offset = arr in
    let (s, b) = !s_ref in
    let s = Seq.upd s (offset + i) (Some x) in
    s_ref := (s, b);
    gst_witness (init_at_pred arr i);
    ()

abstract let write (#a:Type0) (#n:nat) (arr:array a n) (i:nat{i < n}) (x:a)
  :ST unit (requires (fun h0       -> True))  //the array must be mutable
           (ensures  (fun h0 () h1 -> modifies (array_footprint arr) h0 h1 /\  //only array is modified
				   arr `init_at` i                      /\  //witness the stable init predicate
				   Seq.index (as_seq arr h1) i == Some x))  //update the ghost view of the array
  = gst_recall (mutable_pred arr);
    write_common arr i x

(*
 * write into an array
 *)
abstract let fwrite (#a:Type0) (#n:nat) (arr:farray a n) (i:nat{i < n}) (x:a)
  :ST unit (requires (fun h0       -> is_mutable arr h0))  //the array must be mutable
           (ensures  (fun h0 () h1 -> modifies (array_footprint arr) h0 h1 /\  //only array is modified
	                           is_mutable arr h1                    /\  //the array remains mutable
				   arr `init_at` i                      /\  //witness the stable init predicate
				   Seq.index (as_seq arr h1) i == Some x))  //update the ghost view of the array
  = write_common arr i x

(*
 * subarray
 *)
abstract let sub (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (len:nat{i + len <= n}) :t a len
  = let A #m s_ref o = arr in
    A #m s_ref (o + i)

let suffix (#a:Type0) (#n:nat) (arr:array a n) (i:nat{i <= n}) = sub arr i (n - i)
let prefix (#a:Type0) (#n:nat) (arr:array a n) (i:nat{i <= n}) = sub arr 0 i

let lemma_sub_preserves_array_mutable_flag (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (len:nat{i + len <= n})
  :Lemma (requires (witnessed (mutable_pred arr)))
         (ensures  (witnessed (mutable_pred (sub arr i len))))
	 [SMTPat (witnessed (mutable_pred (sub arr i len)))]
  = lemma_functoriality (mutable_pred arr) (mutable_pred (sub arr i len))

let lemma_sub_preserves_array_freezable_flag (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (len:nat{i + len <= n})
  :Lemma (requires (witnessed (freezable_pred arr)))
         (ensures  (witnessed (freezable_pred (sub arr i len))))
	 [SMTPat (witnessed (freezable_pred (sub arr i len)))]
  = lemma_functoriality (freezable_pred arr) (freezable_pred (sub arr i len))

let lemma_sub_is_slice (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (len:nat{i + len <= n}) (h:heap)
  :Lemma (requires True)
         (ensures  (as_seq (sub arr i len) h == Seq.slice (as_seq arr h) i (i + len)))
	 [SMTPat (as_seq (sub arr i len) h)]
  = ()

(*
 * footprint of a subarray is same as the footprint of the array
 *)
let lemma_sub_footprint
  (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (len:nat{i + len <= n})
  :Lemma (requires True)
         (ensures (let arr' = sub arr i len in
                   array_footprint arr == array_footprint arr'))
	  [SMTPat (array_footprint (sub arr i len))]
  = ()

(*
 * a subarray is live iff the array is live
 *)
let lemma_sub_contains
  (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (len:nat{i + len <= n}) (h:heap)
  :Lemma (requires True)
         (ensures  (let arr' = sub arr i len in
	            h `contains_array` arr <==> h `contains_array` arr'))
         [SMTPat (h `contains_array` (sub arr i len))]
  = ()

(*
 * a subarray is mutable iff the array is mutable
 *)
let lemma_sub_is_mutable
  (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (len:nat{i + len <= n}) (h:heap)
  :Lemma (requires True)
         (ensures  (let arr' = sub arr i len in
	            is_mutable arr h <==> is_mutable arr' h))
         [SMTPat (is_mutable (sub arr i len) h)]
  = ()

(*
 * subarray of a frozen array is frozen on a subsequence of the original sequence
 *)
let lemma_sub_frozen
  (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (len:nat{i + len <= n}) (es:erased (Seq.seq a){frozen_with arr es})
  :Lemma (requires True)
         (ensures  (frozen_with (sub arr i len) (hide (Seq.slice (reveal es) i (i + len)))))
	 [SMTPat (frozen_with arr es); SMTPat (sub arr i len)]
  = let arr' = sub arr i len in
    let es'  = hide (Seq.slice (reveal es) i (i + len)) in
    lemma_functoriality (frozen_pred arr es) (frozen_pred arr' es')

(*
 * if a subarray contains an init location, it remains init
 *)
let lemma_sub_init_at
  (#a:Type0) (#n:nat) (arr:t a n) (i:index arr{arr `init_at` i})
  (j:index arr{j <= i}) (len:nat{j + len <= n /\ j + len > i})
  :Lemma (requires True)
         (ensures  ((sub arr j len) `init_at` (i - j)))
	 [SMTPat (arr `init_at` i); SMTPat (sub arr j len)]
  = let arr' = sub arr j len in
    lemma_functoriality (init_at_pred arr i) (init_at_pred arr' (i - j))

(* recall various properties *)
abstract let recall_init (#a:Type0) (#n:nat) (arr:t a n) (i:index arr{arr `init_at` i})
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ Some? (Seq.index (as_seq arr h0) i)))
  = let h0 = ST.get () in
    gst_recall (init_at_pred arr i)

abstract let recall_frozen (#a:Type0) (#n:nat) (arr:t a n) (es:erased (Seq.seq a){frozen_with arr es})
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ some_equivalent_seqs (as_seq arr h0) (reveal es)))
  = let h0 = ST.get () in
    gst_recall (frozen_pred arr es)

abstract let recall_contains (#a:Type0) (#n:nat) (arr:t a n)
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ h0 `contains_array` arr))
  = let A #_ #_ #_ s_ref _ = arr in
    ST.recall s_ref

(* frozen implies init_at at all indices *)
let lemma_frozen_implies_init_at (#a:Type0) (#n:nat) (arr:t a n) (es:erased (Seq.seq a){frozen_with arr es}) (i:index arr)
  :Lemma (requires True)
         (ensures  (arr `init_at` i))
	 [SMTPat (frozen_with arr es); SMTPat (arr `init_at` i)]
  = lemma_functoriality (frozen_pred arr es) (init_at_pred arr i)

(***** some utility functions *****)

let all_init_i_j (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (j:nat{j >= i /\ j <= n}) :Type0
  = forall (k:nat). k >= i /\ k < j ==> arr `init_at` k

let all_init (#a:Type0) (#n:nat) (arr:t a n) :Type0
  = all_init_i_j arr 0 n

let init_arr_in_heap_i_j (#a:Type0) (#n:nat) (arr:t a n) (h:heap) (i:nat) (j:nat{j >= i /\ j <= n}) :Type0
  = forall (k:nat). (k >= i /\ k < j) ==> init_at_seq (as_seq arr h) k

let init_arr_in_heap (#a:Type0) (#n:nat) (arr:t a n) (h:heap) :Type0
  = init_arr_in_heap_i_j arr h 0 n

abstract let recall_all_init_i_j (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (j:nat{j >= i /\ j <= n /\ all_init_i_j arr i j})
  :ST unit (requires (fun _ -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ init_arr_in_heap_i_j arr h0 i j))
  = let rec aux (curr:nat{curr >= i /\ curr < j})
      :ST unit (requires (fun h0      -> init_arr_in_heap_i_j arr h0 i curr))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ init_arr_in_heap_i_j arr h0 i j))
      = gst_recall (init_at_pred arr curr);
        if curr = j - 1 then () else aux (curr + 1)
    in
    if i = j then ()
    else aux i

abstract let recall_all_init (#a:Type0) (#n:nat) (arr:t a n{all_init arr})
  :ST unit (requires (fun _ -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ init_arr_in_heap arr h0))
  = recall_all_init_i_j arr 0 n

abstract let witness_all_init_i_j (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (j:nat{j >= i /\ j <= n})
  :ST unit (requires (fun h0      -> init_arr_in_heap_i_j arr h0 i j))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ all_init_i_j arr i j))
  = let rec aux (curr:nat{curr >= i /\ curr < j})
      :ST unit (requires (fun h0      -> init_arr_in_heap_i_j arr h0 i j /\ all_init_i_j arr i curr))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ all_init_i_j arr i j))
      = recall_contains arr;
        gst_witness (init_at_pred arr curr);
        if curr = j - 1 then () else aux (curr + 1)
    in
    if i = j then ()
    else aux i

abstract let witness_all_init (#a:Type0) (#n:nat) (arr:t a n)
  :ST unit (requires (fun h0 -> init_arr_in_heap arr h0))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ all_init arr))
  = witness_all_init_i_j arr 0 n

let as_initialized_seq
  (#a:Type0) (#n:nat) (arr:t a n) (h:heap{init_arr_in_heap arr h})
  :GTot (seq a)
  = let s = as_seq arr h in
    get_some_equivalent s

let as_initialized_subseq (#a:Type0) (#n:nat) (arr:t a n) (h:heap)
  (i:nat) (j:nat{j >= i /\ j <= n /\ init_arr_in_heap_i_j arr h i j})
  :GTot (seq a)
  = let s = as_seq arr h in
    let s = Seq.slice s i j in
    get_some_equivalent s

abstract let read_subseq_i_j (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (j:nat{j >= i /\ j <= n})
  :ST (seq a)
      (requires (fun h0      -> all_init_i_j arr i j))
      (ensures  (fun h0 s h1 -> h0 == h1                        /\
                             init_arr_in_heap_i_j arr h0 i j /\
                             s == as_initialized_subseq arr h0 i j))
  = let A #_ #_ #_ s_ref off = arr in
    let (s, _) = !s_ref in
    let s = Seq.slice s off (off + n) in
    recall_all_init_i_j arr i j;
    let s = Seq.slice s i j in
    let s = get_some_equivalent s in
    s

private let fill_common (#a:Type0) (#n:nat) (arr:t a n) (buf:seq a{Seq.length buf <= n})
  :ST unit (requires (fun h0      -> is_mutable arr h0))
           (ensures  (fun h0 _ h1 -> modifies (array_footprint arr) h0 h1                   /\
	                          all_init_i_j arr 0 (Seq.length buf)                    /\
				  init_arr_in_heap_i_j arr h1 0 (Seq.length buf)         /\
				  buf == as_initialized_subseq arr h1 0 (Seq.length buf) /\
				  is_mutable arr h1))
  = let A #_ #_ #m s_ref off = arr in
    let (s, b) = !s_ref in
    let s1 = copy_seq s off (off + Seq.length buf) buf in
    s_ref := (s1, b);
    witness_all_init_i_j arr 0 (Seq.length buf);
    lemma_get_equivalent_sequence_slice s1 off (off + Seq.length buf) buf

abstract let fill (#a:Type0) (#n:nat) (arr:array a n) (buf:seq a{Seq.length buf <= n})
  :ST unit (requires (fun h0      -> True))
           (ensures  (fun h0 _ h1 -> modifies (array_footprint arr) h0 h1                   /\
	                          all_init_i_j arr 0 (Seq.length buf)                    /\
				  init_arr_in_heap_i_j arr h1 0 (Seq.length buf)         /\
				  buf == as_initialized_subseq arr h1 0 (Seq.length buf) /\
				  is_mutable arr h1))
  = gst_recall (mutable_pred arr);
    fill_common arr buf

abstract let ffill (#a:Type0) (#n:nat) (arr:farray a n) (buf:seq a{Seq.length buf <= n})
  :ST unit (requires (fun h0      -> is_mutable arr h0))
           (ensures  (fun h0 _ h1 -> modifies (array_footprint arr) h0 h1                   /\
	                          all_init_i_j arr 0 (Seq.length buf)                    /\
				  init_arr_in_heap_i_j arr h1 0 (Seq.length buf)         /\
				  buf == as_initialized_subseq arr h1 0 (Seq.length buf) /\
				  is_mutable arr h1))
  = fill_common arr buf
    
let lemma_framing_of_is_mutable (#a:Type0) (#n:nat) (arr:t a n) (h0:heap) (h1:heap) (r:Set.set nat)
  :Lemma (requires (modifies r h0 h1 /\ Set.disjoint r (array_footprint arr) /\ h0 `contains_array` arr))
         (ensures  ((is_mutable arr h0 <==> is_mutable arr h1) /\
	            (as_seq arr h0 == as_seq arr h1)))
	 [SMTPat (modifies r h0 h1); SMTPat (is_mutable arr h0)]
  = ()

let lemma_framing_of_as_seq (#a:Type0) (#n:nat) (arr:t a n) (h0:heap) (h1:heap) (r:Set.set nat)
  :Lemma (requires (modifies r h0 h1 /\ Set.disjoint r (array_footprint arr) /\ h0 `contains_array` arr))
         (ensures  (as_seq arr h0 == as_seq arr h1))
	 [SMTPat (modifies r h0 h1); SMTPat (as_seq arr h0)]
  = ()

let lemma_all_init_i_j_sub
  (#a:Type0) (#n:nat) (arr:t a n{all_init arr}) (i:nat) (len:nat{i + len <= n})
  :Lemma (requires True)
         (ensures  (all_init (sub arr i len)))
	 [SMTPat (all_init arr); SMTPat (sub arr i len)]
  = let arr' = sub arr i len in

    let aux (k:nat{k < len /\ arr `init_at` (k + i)}) :Lemma (arr' `init_at` k)
      = lemma_sub_init_at arr (k + i) i len
    in
    FStar.Classical.forall_intro aux
