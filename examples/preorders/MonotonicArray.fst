module MonotonicArray

open FStar.Preorder
open FStar.Heap
open FStar.ST

module Set = FStar.Set

open FStar.Seq

open ArrayUtils

private type flag =
  | AlwaysMutable
  | MutableUntilFrozen

private type set_n (n:nat) = (s:set nat{forall (i:nat).{:pattern (Set.mem i s)} Set.mem i s ==> (i >= 0 /\ i < n)})

assume val set_i_j (n:nat) (i:nat) (j:nat{j >= i /\ j <= n})
  :Tot (s:set_n n{forall (k:nat).{:pattern (Set.mem k s)} Set.mem k s <==> k >= i /\ k < j})

assume val scale_down (m:nat) (n:nat) (s:set_n m) (offset:nat{offset + n <= m})
  :Tot (r:set_n n{forall (i:nat).{:pattern (Set.mem i r) \/ Set.mem (offset + i) s} Set.mem i r <==> Set.mem (offset + i) s})

assume val scale_up (m:nat) (n:nat) (s:set_n n) (offset:nat{offset + n <= m})
  :Tot (r:set_n m{forall (i:nat).{:pattern (Set.mem i s) \/ Set.mem (offset + i) r} Set.mem i s <==> Set.mem (offset + i) r})

assume val lemma_scale_up_of_i_j (m:nat) (n:nat) (i:nat) (j:nat{j >= i /\ j <= n}) (offset:nat{offset + n <= m})
  :Lemma (scale_up m n (set_i_j n i j) offset == set_i_j m (offset + i) (offset + j))

assume val lemma_down_up_identity (m:nat) (n:nat) (s:set_n m) (offset:nat{offset + n <= m})
  :Lemma (requires True)
         (ensures  (scale_up m n (scale_down m n s offset) offset == s))
	 [SMTPat (scale_up m n (scale_down m n s offset) offset == s)]

assume val lemma_up_down_identity (m:nat) (n:nat) (s:set_n n) (offset:nat{offset + n <= m})
  :Lemma (requires True)
         (ensures  (scale_down m n (scale_up m n s offset) offset == s))
	 [SMTPat (scale_down m n (scale_up m n s offset) offset == s)]

assume val lemma_scale_up_commutes_with_union (m:nat) (n:nat) (s1:set_n n) (s2:set_n n) (offset:nat{offset + n <= m})
  :Lemma (requires True)
         (ensures  (scale_up m n (Set.union s1 s2) offset == Set.union (scale_up m n s1 offset) (scale_up m n s2 offset)))
	 [SMTPatOr [[SMTPat (scale_up m n (Set.union s1 s2) offset)]; [SMTPat (Set.union (scale_up m n s1 offset) (scale_up m n s2 offset))]]]

assume val lemma_scale_down_commutes_with_union (m:nat) (n:nat) (s1:set_n m) (s2:set_n m) (offset:nat{offset + n <= m})
  :Lemma (requires True)
         (ensures  (scale_down m n (Set.union s1 s2) offset == Set.union (scale_down m n s1 offset) (scale_down m n s2 offset)))
	 [SMTPatOr [[SMTPat (scale_down m n (Set.union s1 s2) offset)]; [SMTPat (Set.union (scale_down m n s1 offset) (scale_up m n s2 offset))]]]

(* seq (option a) is the contents, flag is the flag above, set nat is the indices frozen currently *)
noeq private type repr (a:Type0) (n:nat) :Type0 =
  | Repr: s:seq (option a){length s == n}
          -> f:flag
          -> i_indices: set_n n{forall (i:nat{i >= 0 /\ i < n}).{:pattern (Set.mem i i_indices) \/ Some? (index s i)} Set.mem i i_indices <==> Some? (index s i)}  //set of initialized indices
	  -> f_indices:set_n n{Set.subset f_indices i_indices /\
	                      (f == AlwaysMutable ==> f_indices == Set.empty)}  //set of frozen indices
	  -> repr a n

private type repr_rel (a:Type0) (n:nat) :relation (repr a n)
  = fun (t1:repr a n) (t2:repr a n) -> let Repr s1 f1 i_indices1 f_indices1 = t1 in
                                    let Repr s2 f2 i_indices2 f_indices2 = t2 in
                                    f1 == f2                         /\  //flag remains same
				    Set.subset i_indices1 i_indices2 /\
                                    Set.subset f_indices1 f_indices2 /\  //and both sets increase monotonically
				    (forall (i:nat).{:pattern (Set.mem i f_indices1)}
				              Set.mem i f_indices1 ==> index s1 i == index s2 i)  //and frozen indices remain same (note that we get init indices remain init from subset on i_indices, and refinement on the repr

(* typing the relation above as preorder *)
private let repr_pre (a:Type0) (n:nat) :preorder (repr a n) = repr_rel a n

(*
 * an array is a mref and an offset into the array (for taking interior pointers)
 * the view of an array is from offset to m
 *)
noeq abstract type t (a:Type0) (n:nat) =
  | A: #m:nat
       -> s_ref:mref (repr a m) (repr_pre a m)
       -> offset:nat{offset + n <= m} -> t a n

abstract type always_mutable_pred_ (#a:Type0) (#n:nat) (x:t a n) :heap_predicate
  = fun h ->
    let A r_ref _ = x in
    h `Heap.contains` r_ref /\ (let Repr _ f _ _ = sel h r_ref in f == AlwaysMutable)

abstract type always_mutable_pred (#a:Type0) (#n:nat) (x:t a n) :(p:heap_predicate{stable p})
  = always_mutable_pred_ x

abstract type freezable_pred_ (#a:Type0) (#n:nat) (x:t a n) (s:set_n n) :heap_predicate
  = fun h ->
    let A r_ref offset = x in
    h `Heap.contains` r_ref /\ (let Repr _ f _ f_indices = sel h r_ref in
                               f == MutableUntilFrozen /\
			       scale_down

abstract type freezable_pred (#a:Type0) (#n:nat) (x:t a n) :(p:heap_predicate{stable p})
  = freezable_pred_ x

type farray (a:Type0) (n:nat) = (x:t a n{witnessed (freezable_pred x)})a  //an array that can be frozen (in part)

type array (a:Type0) (n:nat) = x:t a n{witnessed (always_mutable_pred x)}  //an array that you don't intend to freeze

abstract let array_footprint (#a:Type0) (#n:nat) (arr:t a n) :GTot (Set.set nat)
  = let A r_ref _ = arr in
    Set.singleton (addr_of r_ref)

abstract let contains_array (#a:Type) (#n:nat) (h:heap) (arr:t a n)
  = let A r_ref _ = arr in
    h `Heap.contains` r_ref

let fresh_arr (#a:Type0) (#n:nat) (arr:t a n) (h0 h1:heap)
  = h1 `contains_array` arr /\  //array is live in h1
    (forall (n:nat).{:pattern (Set.mem n (array_footprint arr))} Set.mem n (array_footprint arr) ==> n `addr_unused_in` h0)  //the footprint of array was unused in h0, hopefully this enables the clients to maintain separation

(*
 * create an array that you intend to freeze in part
 *)
abstract let fcreate (a:Type0) (n:nat)
  :ST (farray a n) (requires (fun _         -> True))
                   (ensures  (fun h0 arr h1 -> fresh_arr arr h0 h1      /\  //it's fresh
		                            modifies Set.empty h0 h1))  //no existing refs are changed
  = let arr = A #a #n #n (alloc (Repr (Seq.create n None) MutableUntilFrozen Set.empty Set.empty)) 0 in
    gst_witness (freezable_pred arr);
    arr

(*
 * create an array, that always remains mutable
 *)
abstract let create (a:Type0) (n:nat)
  :ST (array a n) (requires (fun _         -> True))
                  (ensures  (fun h0 arr h1 -> fresh_arr arr h0 h1      /\  //it's fresh
		                           modifies Set.empty h0 h1))  //no existing refs are changed
  = let arr = A #a #n #n (alloc (Repr (Seq.create n None) AlwaysMutable Set.empty Set.empty)) 0 in
    gst_witness (always_mutable_pred arr);
    arr

(*
 * Ghost view of an array as a sequence of options
 *)
abstract let as_seq (#a:Type0) (#n:nat) (arr:t a n) (h:heap)
  :GTot (s:Seq.seq (option a))
  = let A #_ #_ #_ s_ref off = arr in
    let s = Repr?.s (sel h s_ref) in
    Seq.slice s off (off + n)

let lemma_as_seq_length (#a:Type0) (#n:nat) (arr:t a n) (h:heap)
  :Lemma (requires True)
         (ensures  (Seq.length (as_seq arr h) = n))
	 [SMTPat (Seq.length (as_seq arr h))]
  = ()

private let init_at_pred_ (#a:Type0) (#n:nat) (arr:t a n) (s:set_n n) :heap_predicate
  = fun h -> h `contains_array` arr /\
          (let A #_ #_ #m r_ref offset = arr in
	   let Repr _ _ i_indices _ = sel h r_ref in
	   Set.subset (scale_up m n s offset) i_indices)

(* a stable init_at predicate *)
abstract let init_at_pred (#a:Type0) (#n:nat) (arr:t a n) (s:set_n n) :(p:heap_predicate{stable p})
  = init_at_pred_ arr s

(* witnessed predicate for init_at *)
abstract let init_at (#a:Type0) (#n:nat) (arr:t a n) (s:set_n n) :Type0
  = witnessed (init_at_pred arr s)

open FStar.Ghost

private let frozen_at_pred_ (#a:Type0) (#n:nat) (arr:t a n) (s:set_n n) (snap:erased (seq (option a)))
  :heap_predicate
  = let snap = reveal snap in
    fun h -> h `contains_array` arr /\ length snap == n /\
          (let A #_ #_ #m r_ref offset = arr in
	   let Repr l _ _ f_indices = sel h r_ref in
	   Set.subset (scale_up m n s offset) f_indices /\
	   (forall (i:nat).{:pattern (Set.mem i s)} Set.mem i s ==> index snap i == index l (offset + i)))

(* a stable init_at predicate *)
abstract let frozen_at_pred (#a:Type0) (#n:nat) (arr:t a n) (s:set_n n) (snap:erased (seq (option a)))
  :(p:heap_predicate{stable p})
  = let A #_ #_ #m r_ref offset = arr in
    assert (forall (h1 h2:heap).
              (h1 `Heap.contains` r_ref /\ heap_rel h1 h2) ==>
	       (let Repr l1 _ _ f_indices1 = sel h1 r_ref in
	        let Repr l2 _ _ _ = sel h2 r_ref in
		(forall (i:nat). Set.mem i f_indices1 ==> index l1 i == index l2 i)));
  frozen_at_pred_ arr s snap

(* witnessed predicate for init_at *)
abstract let frozen_at (#a:Type0) (#n:nat) (arr:t a n) (s:set_n n) (snap:erased (seq (option a))) :Type0
  = witnessed (frozen_at_pred arr s snap)

(***** serious stuff starts now *****)


(*** Doesn't work below this ***)

abstract let freeze (#a:Type0) (#n:nat) (arr:farray a n) (s:set_n n)
  :ST (set_n n * erased (seq (option a)))
      (requires (fun _      -> init_at arr s))
      (ensures (fun h0 r h1 -> let rs, rl = fst r, reveal (snd r) in
                            length rl == n                        /\
                            modifies (array_footprint arr) h0 h1  /\
			    Set.subset s rs                       /\
                            frozen_at arr rs (hide rl)))
  = gst_recall (freezable_pred arr);  //recall that the array is freezable
    gst_recall (init_at_pred arr s);  //recall that all indices in s are initialized
    let A #_ #_ #m s_ref offset = arr in
    let Repr l flag i_indices f_indices = !s_ref in
    let f_indices = Set.union f_indices (scale_up m n s offset) in  //add s to frozen indices
    s_ref := Repr l flag i_indices f_indices;  //write the updated repr
    let rs = scale_down m n f_indices offset in  //scale the frozen set
    let rl = Seq.slice l offset (offset + n) in  //slice the underlying seq
    lemma_down_up_identity m n f_indices offset;  //TODO: why is this lemma not firing
    gst_witness (frozen_at_pred arr rs (hide rl));  //witness frozen predicate
    (rs, hide rl)  //boom!

abstract let recall_frozen_i (#a:Type0) (#n:nat) (arr:farray a n)
  (s:set_n n) (l:erased (seq (option a))) (i:nat{Set.mem i s})
  :ST unit (fun _       -> frozen_at arr s l)
           (fun h0 _ h1 -> h0 == h1 /\ length (reveal l) == n /\ index (as_seq arr h0) i == index (reveal l) i)
  = gst_recall (frozen_at_pred arr s l)

let init_arr_in_heap_i_j (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (j:nat{j >= i /\ j <= n}) (h:heap) :Type0
  = forall (k:nat{k >= i /\ k < j}).{:pattern (index (as_seq arr h) k)} Some? (index (as_seq arr h) k)

let as_initialized_subseq (#a:Type0) (#n:nat) (arr:t a n) (h:heap)
  (i:nat) (j:nat{j >= i /\ j <= n /\ init_arr_in_heap_i_j arr i j h})
  :GTot (seq a)
  = let s = as_seq arr h in
    let s = Seq.slice s i j in
    get_some_equivalent s

abstract let read (#a:Type0) (#n:nat) (arr:t a n) (i:nat) (j:nat{j >= i /\ j <= n})
  :ST (seq a)
      (requires (fun _       -> init_at arr (set_i_j n i j)))
      (ensures  (fun h0 s h1 -> h0 == h1                        /\
                             init_arr_in_heap_i_j arr i j h0 /\
                             s == as_initialized_subseq arr h0 i j))
  = gst_recall (init_at_pred arr (set_i_j n i j));
    let A #_ #_ #m s_ref offset = arr in
    lemma_scale_up_of_i_j m n i j offset;
    let Repr s _ _ _ = !s_ref in
    let s = Seq.slice s (offset + i) (offset + j) in    
    get_some_equivalent s

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

let suffix (#a:Type0) (#n:nat) (arr:t a n) (i:nat{i <= n}) = sub arr i (n - i)
let prefix (#a:Type0) (#n:nat) (arr:t a n) (i:nat{i <= n}) = sub arr 0 i

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

(***** disjointness *****)

abstract let disjoint_sibling (#a:Type0) (#n1:nat) (#n2:nat) (arr1:t a n1) (arr2:t a n2) :Type0
  = let A #_ #_ #m1 s_ref1 off1 = arr1 in
    let A #_ #_ #m2 s_ref2 off2 = arr2 in

    m1 == m2 /\ s_ref1 === s_ref2  /\
    ((off1 + n1 <= off2) \/
     (off2 + n2 <= off1))

let lemma_disjoint_sibling_suffix_prefix (#a:Type0) (#n:nat) (arr:t a n) (pos:nat{pos <= n})
  :Lemma (disjoint_sibling (prefix arr pos) (suffix arr pos) /\
          disjoint_sibling (suffix arr pos) (prefix arr pos))
  = ()

let disjoint_siblings_remain_same (#a:Type0) (#n:nat) (arr:t a n) (h0 h1:heap)
  = forall (m:nat) (arr':t a m). disjoint_sibling arr arr' ==> (as_seq arr' h0 == as_seq arr' h1)

let lemma_disjoint_sibling_remain_same_for_unrelated_mods
  (#a:Type0) (#n:nat) (arr:t a n) (r:Set.set nat{Set.disjoint r (array_footprint arr)}) (h0:heap) (h1:heap{modifies r h0 h1})
  :Lemma (requires (h0 `contains_array` arr))
         (ensures (disjoint_siblings_remain_same arr h0 h1))
  = ()

let lemma_disjoint_sibling_remain_same_transitive
  (#a:Type0) (#n:nat) (arr:t a n) (h0 h1 h2:heap)
  :Lemma (requires (disjoint_siblings_remain_same arr h0 h1 /\ disjoint_siblings_remain_same arr h1 h2))
         (ensures  (disjoint_siblings_remain_same arr h0 h2))
  = ()

#set-options "--z3rlimit 100"
private let fill_common (#a:Type0) (#n:nat) (arr:t a n) (buf:seq a{Seq.length buf <= n})
  :ST unit (requires (fun h0      -> is_mutable arr h0))
           (ensures  (fun h0 _ h1 -> modifies (array_footprint arr) h0 h1                   /\
	                          all_init_i_j arr 0 (Seq.length buf)                    /\
				  init_arr_in_heap_i_j arr h1 0 (Seq.length buf)         /\
				  buf == as_initialized_subseq arr h1 0 (Seq.length buf) /\
				  is_mutable arr h1                                      /\
				  disjoint_siblings_remain_same arr h0 h1))
  = let h0 = get () in
    let A #_ #_ #m s_ref off = arr in
    let (s, b) = !s_ref in
    let s1 = copy_seq s off (off + Seq.length buf) buf in
    assert (forall (off1:nat) (n1:nat). ((off1 + n1 <= m) /\ (off1 + n1 <= off \/ off + n <= off1)) ==>
                                Seq.slice s off1 (off1 + n1) == Seq.slice s1 off1 (off1 + n1));
    s_ref := (s1, b);
    let h1 = ST.get () in
    witness_all_init_i_j arr 0 (Seq.length buf);
    lemma_get_equivalent_sequence_slice s1 off (off + Seq.length buf) buf;
    assert (forall (n1:nat) (arr1:t a n1). disjoint_sibling arr arr1 ==>
                                   (let A #_ #_ #m1 s_ref1 off1 = arr1 in
				    m1 == m /\ s_ref1 === s_ref /\ (off1 + n1 <= off \/ off + n <= off1) /\
				    as_seq arr1 h0 == Seq.slice s off1 (off1 + n1) /\
				    as_seq arr1 h1 == Seq.slice s1 off1 (off1 + n1)));
    ()

#reset-options
abstract let fill (#a:Type0) (#n:nat) (arr:array a n) (buf:seq a{Seq.length buf <= n})
  :ST unit (requires (fun h0      -> True))
           (ensures  (fun h0 _ h1 -> modifies (array_footprint arr) h0 h1                   /\
	                          all_init_i_j arr 0 (Seq.length buf)                    /\
				  init_arr_in_heap_i_j arr h1 0 (Seq.length buf)         /\
				  buf == as_initialized_subseq arr h1 0 (Seq.length buf) /\
				  is_mutable arr h1                                      /\
				  disjoint_siblings_remain_same arr h0 h1))
  = gst_recall (mutable_pred arr);
    fill_common arr buf

abstract let ffill (#a:Type0) (#n:nat) (arr:farray a n) (buf:seq a{Seq.length buf <= n})
  :ST unit (requires (fun h0      -> is_mutable arr h0))
           (ensures  (fun h0 _ h1 -> modifies (array_footprint arr) h0 h1                   /\
	                          all_init_i_j arr 0 (Seq.length buf)                    /\
				  init_arr_in_heap_i_j arr h1 0 (Seq.length buf)         /\
				  buf == as_initialized_subseq arr h1 0 (Seq.length buf) /\
				  is_mutable arr h1                                      /\
				  disjoint_siblings_remain_same arr h0 h1))
  = fill_common arr buf
