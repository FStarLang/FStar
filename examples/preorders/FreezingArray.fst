module FreezingArray

open FStar.Preorder
open FStar.Heap
open FStar.ST

module Seq = FStar.Seq
module Set = FStar.Set

type seq = Seq.seq

(*
 * representation of an array, a sequence of options and a bool, with an invariant that
 * if the bool is set, the sequence is all Some
 * the bool represents the frozen bit
 *)
private type repr (a:Type0) (n:nat) :Type0 =
  t:(Seq.seq (option a) * bool){Seq.length (fst t) = n /\ (b2t (snd t) ==> (forall (i:nat). i < n ==> Some? (Seq.index (fst t) i)))}

(*
 * relation (preorder) between sequences
 * if b1 is set, b2 is also set, and the sequences remain same (frozen)
 * in any case, once a sequence entry is Some, it remains Some
 *)
private type seq_rel (a:Type0) (n:nat) :relation (repr a n)
  = fun (t1:repr a n) (t2:repr a n) -> let s1, b1 = t1 in
                                    let s2, b2 = t2 in
				    (b2t b1 ==> (b2t b2 /\ (s1 == s2))) /\  //once the seq is init, it remains init
				    (forall (i:nat). i < n ==> (Some? (Seq.index s1 i) ==>
				                         Some? (Seq.index s2 i)))  //in any case, Some indices remain Some

(* typing the relation above as preorder *)
private let seq_pre (a:Type0) (n:nat) :preorder (repr a n) = seq_rel a n

(*
 * an array is a mref and an offset into the array (for taking interior pointers)
 * the view of an array is from offset to m
 *)
noeq abstract type array (a:Type0) (n:nat) =
  | A: #m:nat -> s_ref:mref (repr a m) (seq_pre a m)
       -> offset:nat{offset + n <= m} -> array a n

(*
 * this is true if the current array has full view of the underlying array
 * we currently require freezing only on the full array
 *)
abstract let is_full_array (#a:Type0) (#n:nat) (arr:array a n) :bool =
  let A #_ #_ #m _ off = arr in
  off = 0 && n = m

(*
 * footprint of the array in the heap
 *)
abstract let array_footprint (#a:Type0) (#n:nat) (arr:array a n) :GTot (Set.set nat)
  = let A s_ref _ = arr in
    Set.singleton (addr_of s_ref)

(*
 * liveness of an array in the heap
 *)
abstract let contains_array (#a:Type) (#n:nat) (h:heap) (arr:array a n)
  = let A #_ #_ #_ s_ref _ = arr in
    h `contains` s_ref

(*
 * this is a precondition for writing, essentially, it will be false once you freeze the array
 *)
abstract let is_mutable (#a:Type0) (#n:nat) (arr:array a n) (h:heap)
  = let A #_ s_ref _ = arr in
    not (snd (sel h s_ref))

let fresh_arr (#a:Type0) (#n:nat) (arr:array a n) (h0 h1:heap)
  = h1 `contains_array` arr /\  //array is live in h1
    (forall (n:nat). Set.mem n (array_footprint arr) ==> n `addr_unused_in` h0)  //the footprint of array was unused in h0, hopefully this enables the clients to maintain separation

(*
 * create an array
 *)
abstract let create (a:Type0) (n:nat)
  :ST (array a n) (requires (fun _         -> True))
                  (ensures  (fun h0 arr h1 -> fresh_arr arr h0 h1      /\  //it's fresh
		                           modifies Set.empty h0 h1 /\  //no existing refs are changed
					   is_mutable arr h1        /\  //the array is mutable
					   is_full_array arr))         //and has the full view of the underlying sequence
  = A #a #n #n (alloc ((Seq.create n None), false)) 0

(*
 * type of a valid index into an array
 *)
type index (#a:Type0) (#n:nat) (arr:array a n) = i:nat{i < n}

(*
 * Ghost view of an array as a sequence of options
 *)
abstract let as_seq (#a:Type0) (#n:nat) (arr:array a n) (h:heap)
  :GTot (s:Seq.seq (option a))
  = let A #_ #_ #_ s_ref off = arr in
    let s = fst (sel h s_ref) in
    Seq.slice s off (off + n)

let lemma_as_seq_length (#a:Type0) (#n:nat) (arr:array a n) (h:heap)
  :Lemma (requires True)
         (ensures  (Seq.length (as_seq arr h) = n))
	 [SMTPat (Seq.length (as_seq arr h))]
  = ()

(*
 * a sequence of option a is equivalent to a sequence of a, if all are Some and contained values match
 *)
let equivalent_seqs (#a:Type0) (s1:Seq.seq (option a)) (s2:Seq.seq a) :Type0
  = (Seq.length s1 == Seq.length s2) /\
    (forall (i:nat). i < Seq.length s1 ==> Some (Seq.index s2 i) == Seq.index s1 i)

let equivalent_seqs_lemma (#a:Type0) (s1:Seq.seq (option a)) (s2:Seq.seq a)
  :Lemma (requires (equivalent_seqs s1 s2))
         (ensures  (forall (i:nat). i < Seq.length s1 ==> Some? (Seq.index s1 i)))
	 [SMTPat (equivalent_seqs s1 s2)]
  = ()

(* scaffolding for init_at *)
let init_at_seq (#a:Type0) (s:Seq.seq (option a)) (i:nat{i < Seq.length s}) :Type0
  = Some? (Seq.index s i)

abstract let init_at_arr (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) (h:heap) :Type0
  = let s = as_seq arr h in
    init_at_seq s i

private let init_at_pred' (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) :heap_predicate
  = fun h -> h `contains_array` arr /\ init_at_arr arr i h

(* a stable init_at predicate *)
abstract let init_at_pred (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) :(p:heap_predicate{stable p})
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
abstract let init_at (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) :Type0
  = witnessed (init_at_pred arr i)

(* assuming this function, quite straightforward, just strip out the Some *)
assume val get_equivalent_seq (#a:Type0) (s:Seq.seq (option a){forall (i:nat). i < Seq.length s ==> Some? (Seq.index s i)})
  :Tot (r:Seq.seq a{equivalent_seqs s r})

assume val lemma_equivalent_implies_slice_equivalent
  (#a:Type0) (s1:seq (option a)) (s2:seq a{equivalent_seqs s1 s2})
  (i:nat) (j:nat{j >= i /\ j < Seq.length s1})
  :Lemma (requires True)
         (ensures  (equivalent_seqs (Seq.slice s1 i j) (Seq.slice s2 i j)))
	 [SMTPat (equivalent_seqs (Seq.slice s1 i j) (Seq.slice s2 i j))]

assume val lemma_get_equivalent_commutes_with_slice
  (#a:Type0) (s:seq (option a){forall (i:nat). i < Seq.length s ==> Some? (Seq.index s i)}) (i:nat) (j:nat{j >= i /\ j < Seq.length s})
  :Lemma (requires True)
         (ensures  (Seq.slice (get_equivalent_seq s) i j == get_equivalent_seq (Seq.slice s i j)))
	 [SMTPatOr [[SMTPat (Seq.slice (get_equivalent_seq s) i j)]; [SMTPat (get_equivalent_seq (Seq.slice s i j))]]]

assume val lemma_get_equivalent_sequence_slice
  (#a:Type0) (s:seq (option a)) (i:nat) (j:nat{j >= i /\ j <= Seq.length s})
  (s':seq a{Seq.length s' = j - i /\ (forall (k:nat). (k >= i /\ k < j) ==> Seq.index s k == Some (Seq.index s' (k - i)))})
  :Lemma (requires True)
         (ensures  (get_equivalent_seq (Seq.slice s i j) == s'))

(* scaffolding for frozen predicate *)
abstract let frozen_bit (#a:Type0) (#n:nat) (arr:array a n) (h:heap) :GTot bool
  = let A s_ref _ = arr in
    snd (sel h s_ref)

private type frozen_pred' (#a:Type0) (#n:nat) (arr:array a n) (s:Seq.seq a) :heap_predicate
  = fun h -> h `contains_array` arr /\ equivalent_seqs (as_seq arr h) s /\ frozen_bit arr h

open FStar.Ghost

(* a stable frozen predicate *)
abstract type frozen_pred (#a:Type0) (#n:nat) (arr:array a n) (s:erased (Seq.seq a)) :(p:heap_predicate{stable p})
  = frozen_pred' arr (reveal s)

(* witnessed predicate for frozen *)
abstract type frozen_with (#a:Type0) (#n:nat) (arr:array a n) (s:erased (Seq.seq a)) :Type0
  = Seq.length (reveal s) == n /\ witnessed (frozen_pred arr s)

(***** serious stuff starts now *****)

(*
 * freeze an array
 *)
abstract let freeze (#a:Type0) (#n:nat) (arr:array a n)
  :ST (s:erased (Seq.seq a))
      (requires (fun h0       -> is_full_array arr /\  //can only freeze full arrays
                              (forall (i:nat). i < n ==> init_at_arr arr i h0)))  //all elements must be init_at
      (ensures  (fun h0 es h1 -> equivalent_seqs (as_seq arr h0) (reveal es) /\  //the returned ghost sequence is the current view of array in the heap
                              frozen_with arr es                          /\  //witnessing the stable predicate
                              (~ (is_mutable arr h1))                     /\  //the array is no longer mutable
			      modifies (array_footprint arr) h0 h1))  //only array footprint is changed
  = let A #_ s_ref _ = arr in
    let s, b = !s_ref in
    s_ref := (s, true);
    gst_witness (frozen_pred arr (hide (get_equivalent_seq s)));
    hide (get_equivalent_seq s)

(*
 * read from an array
 *)
abstract let read (#a:Type0) (#n:nat) (arr:array a n) (i:index arr{arr `init_at` i})  //the index must be `init_at`
  :ST a (requires (fun h0      -> True))
        (ensures  (fun h0 r h1 -> h0 == h1 /\ Some r == Seq.index (as_seq arr h0) i))
  = let A #_ s_ref o = arr in
    let (s, _) = !s_ref in
    gst_recall (init_at_pred arr i);
    Some?.v (Seq.index s (o + i))

(*
 * write into an array
 *)
abstract let write (#a:Type0) (#n:nat) (arr:array a n) (i:nat{i < n}) (x:a)
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

(*
 * subarray
 *)
abstract let sub (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) (len:nat{i + len <= n}) :array a len
  = let A #m s_ref o = arr in
    A #m s_ref (o + i)

let suffix (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) = sub arr i (n - i)
let prefix (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) = sub arr 0 i

let lemma_sub_is_slice (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) (len:nat{i + len <= n}) (h:heap)
  :Lemma (requires True)
         (ensures  (as_seq (sub arr i len) h == Seq.slice (as_seq arr h) i (i + len)))
	 [SMTPat (as_seq (sub arr i len) h)]
  = ()

(*
 * footprint of a subarray is same as the footprint of the array
 *)
let lemma_sub_footprint
  (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) (len:nat{i + len <= n})
  :Lemma (requires True)
         (ensures (let arr' = sub arr i len in
                   array_footprint arr == array_footprint arr'))
	  [SMTPat (array_footprint (sub arr i len))]
  = ()

(*
 * a subarray is live iff the array is live
 *)
let lemma_sub_contains
  (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) (len:nat{i + len <= n}) (h:heap)
  :Lemma (requires True)
         (ensures  (let arr' = sub arr i len in
	            h `contains_array` arr <==> h `contains_array` arr'))
         [SMTPat (h `contains_array` (sub arr i len))]
  = ()

(*
 * a subarray is mutable iff the array is mutable
 *)
let lemma_sub_is_mutable
  (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) (len:nat{i + len <= n}) (h:heap)
  :Lemma (requires True)
         (ensures  (let arr' = sub arr i len in
	            is_mutable arr h <==> is_mutable arr' h))
         [SMTPat (is_mutable (sub arr i len) h)]
  = ()

(*
 * subarray of a frozen array is frozen on a subsequence of the original sequence
 *)
let lemma_sub_frozen
  (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) (len:nat{i + len <= n}) (es:erased (Seq.seq a){frozen_with arr es})
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
  (#a:Type0) (#n:nat) (arr:array a n) (i:index arr{arr `init_at` i})
  (j:index arr{j <= i}) (len:nat{j + len <= n /\ j + len > i})
  :Lemma (requires True)
         (ensures  ((sub arr j len) `init_at` (i - j)))
	 [SMTPat (arr `init_at` i); SMTPat (sub arr j len)]
  = let arr' = sub arr j len in
    lemma_functoriality (init_at_pred arr i) (init_at_pred arr' (i - j))

(* recall various properties *)
abstract let recall_init (#a:Type0) (#n:nat) (arr:array a n) (i:index arr{arr `init_at` i})
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ Some? (Seq.index (as_seq arr h0) i)))
  = let h0 = ST.get () in
    gst_recall (init_at_pred arr i)

abstract let recall_frozen (#a:Type0) (#n:nat) (arr:array a n) (es:erased (Seq.seq a){frozen_with arr es})
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ equivalent_seqs (as_seq arr h0) (reveal es)))
  = let h0 = ST.get () in
    gst_recall (frozen_pred arr es)

abstract let recall_contains (#a:Type0) (#n:nat) (arr:array a n)
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ h0 `contains_array` arr))
  = let A #_ #_ #_ s_ref _ = arr in
    ST.recall s_ref

(* frozen implies init_at at all indices *)
let lemma_frozen_implies_init_at (#a:Type0) (#n:nat) (arr:array a n) (es:erased (Seq.seq a){frozen_with arr es}) (i:index arr)
  :Lemma (requires True)
         (ensures  (arr `init_at` i))
	 [SMTPat (frozen_with arr es); SMTPat (arr `init_at` i)]
  = lemma_functoriality (frozen_pred arr es) (init_at_pred arr i)

(***** some utility functions *****)

let all_init_i_j (#a:Type0) (#n:nat) (arr:array a n) (i:nat) (j:nat{j >= i /\ j <= n}) :Type0
  = forall (k:nat). k >= i /\ k < j ==> arr `init_at` k

let all_init (#a:Type0) (#n:nat) (arr:array a n) :Type0
  = all_init_i_j arr 0 n

type iarray_i_j (a:Type0) (n:nat) (i:nat) (j:nat{j >= i /\ j <= n}) :Type0
  = arr:array a n{all_init_i_j arr i j}

type iarray (a:Type0) (n:nat) :Type0 = iarray_i_j a n 0 n

abstract let recall_all_init_i_j (#a:Type0) (#n:nat) (arr:array a n) (i:nat) (j:nat{j >= i /\ j <= n /\ all_init_i_j arr i j})
  :ST unit (requires (fun _ -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ (forall (k:nat). k >= i /\ k < j ==> Some? (Seq.index (as_seq arr h0) k))))
  = let rec aux (curr:nat{curr >= i /\ curr < j})
      :ST unit (requires (fun h0      -> forall (k:nat). k >= i /\ k < curr ==> Some? (Seq.index (as_seq arr h0) k)))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ (forall (k:nat). k >= i /\ k < j ==> Some? (Seq.index (as_seq arr h0) k))))
      = gst_recall (init_at_pred arr curr);
        if curr = j - 1 then () else aux (curr + 1)
    in
    if i = j then ()
    else aux i

abstract let recall_all_init (#a:Type0) (#n:nat) (arr:array a n{all_init arr})
  :ST unit (requires (fun _ -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ (forall (i:nat). i < n ==> Some? (Seq.index (as_seq arr h0) i))))
  = recall_all_init_i_j arr 0 n

abstract let witness_all_init_i_j (#a:Type0) (#n:nat) (arr:array a n) (i:nat) (j:nat{j >= i /\ j <= n})
  :ST unit (requires (fun h0      -> forall (k:nat). k >= i /\ k < j ==> Some? (Seq.index (as_seq arr h0) k)))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ all_init_i_j arr i j))
  = let rec aux (curr:nat{curr >= i /\ curr < j})
      :ST unit (requires (fun h0      -> (forall (k:nat). k >= i /\ k < j ==> Some? (Seq.index (as_seq arr h0) k)) /\ all_init_i_j arr i curr))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ all_init_i_j arr i j))
      = recall_contains arr;
        gst_witness (init_at_pred arr curr);
        if curr = j - 1 then () else aux (curr + 1)
    in
    if i = j then ()
    else aux i

abstract let witness_all_init (#a:Type0) (#n:nat) (arr:array a n)
  :ST unit (requires (fun h0 -> forall (k:nat). k < n ==> Some? (Seq.index (as_seq arr h0) k)))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ all_init arr))
  = witness_all_init_i_j arr 0 n

let as_initialized_seq (#a:Type0) (#n:nat) (arr:array a n) (h:heap{forall (i:nat). i < n ==> Some? (Seq.index (as_seq arr h) i)})
  :GTot (seq a)
  = let s = as_seq arr h in
    get_equivalent_seq s

let lemma_as_initialized_seq_gives_equivalent_seq
  (#a:Type0) (#n:nat) (arr:array a n) (h:heap{forall (i:nat). i < n ==> Some? (Seq.index (as_seq arr h) i)})
  :Lemma (requires True)
         (ensures  (equivalent_seqs (as_seq arr h) (as_initialized_seq arr h)))
	 [SMTPat (as_initialized_seq arr h)]
  = ()

let as_initialized_subseq (#a:Type0) (#n:nat) (arr:array a n) (h:heap)
  (i:nat) (j:nat{j >= i /\ j <= n /\ (forall (k:nat). k >= i /\ k < j ==> Some? (Seq.index (as_seq arr h) k))})
  :GTot (seq a)
  = let s = as_seq arr h in
    let s = Seq.slice s i j in
    get_equivalent_seq s

(* let lemma_as_initialized_subseq (#a:Type0) (#n:nat) (arr:array a n) (h:heap{forall (i:nat). i < n ==> Some? (Seq.index (as_seq arr h) i)}) *)
(*   (i:nat) (j:nat{j >= i /\ j <= n}) *)
(*   :Lemma (requires True) *)
(*          (ensures  (let s = as_initialized_subseq arr h i j in *)
(* 	            Seq.length s = j - i /\ s == Seq.slice (as_initialized_seq arr h) i j)) *)
(* 	 [SMTPat (as_initialized_subseq arr h i j)] *)
(*   = () *)

abstract let read_subseq_i_j (#a:Type0) (#n:nat) (arr:array a n) (i:nat) (j:nat{j >= i /\ j <= n})
  :ST (seq a)
      (requires (fun h0      -> all_init_i_j arr i j))
      (ensures  (fun h0 s h1 -> h0 == h1                                                          /\
                             (forall (k:nat). k >= i /\ k < j ==> Some? (Seq.index (as_seq arr h0) k)) /\
                             s == as_initialized_subseq arr h0 i j))
  = let A #_ #_ #_ s_ref off = arr in
    let (s, _) = !s_ref in
    let s = Seq.slice s off (off + n) in
    recall_all_init_i_j arr i j;
    let s = Seq.slice s i j in
    let s = get_equivalent_seq s in
    s

assume val copy_seq (#a:Type0) (s1:seq (option a)) (i:nat) (j:nat) (s2:seq a)
  :Pure (seq (option a))
        (requires (j >= i /\ j <= Seq.length s1 /\ Seq.length s2 = j - i))
	(ensures  (fun r -> j >= i /\ j <= Seq.length s1 /\ Seq.length s2 = j - i /\
	                 Seq.length r == Seq.length s1 /\
                         (forall (k:nat). (k < i ==> (Seq.index r k == Seq.index s1 k)) /\
			            ((k >= i /\ k < j) ==> (Seq.index r k == Some (Seq.index s2 (k - i)))) /\
				    ((k >= j /\ k < Seq.length s1) ==> (Seq.index r k == Seq.index s1 k)))))
	                 //get_equivalent_seq (Seq.slice r i j) == s2))

abstract let fill (#a:Type0) (#n:nat) (arr:array a n) (buf:seq a{Seq.length buf <= n})
  :ST unit (requires (fun h0      -> is_mutable arr h0))
           (ensures  (fun h0 _ h1 -> modifies (array_footprint arr) h0 h1                                  /\
	                          all_init_i_j arr 0 (Seq.length buf)                                   /\
				  (forall (k:nat). k < Seq.length buf ==> Some? (Seq.index (as_seq arr h1) k)) /\
				  buf == as_initialized_subseq arr h1 0 (Seq.length buf)                /\
				  is_mutable arr h1))
  = let A #_ #_ #m s_ref off = arr in
    let (s, b) = !s_ref in
    let s1 = copy_seq s off (off + Seq.length buf) buf in
    s_ref := (s1, b);
    witness_all_init_i_j arr 0 (Seq.length buf);
    lemma_get_equivalent_sequence_slice s1 off (off + Seq.length buf) buf
    
let lemma_framing_of_is_mutable (#a:Type0) (#n:nat) (arr:array a n) (h0:heap) (h1:heap) (r:Set.set nat)
  :Lemma (requires (modifies r h0 h1 /\ Set.disjoint r (array_footprint arr) /\ h0 `contains_array` arr /\ is_mutable arr h0))
         (ensures  (is_mutable arr h1))
	 [SMTPat (modifies r h0 h1); SMTPat (is_mutable arr h0)]
  = ()
