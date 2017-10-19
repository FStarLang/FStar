module FStar.Buffer

open FStar.Seq
open FStar.UInt32
open FStar.StackHeap2
open FStar.StackArray
open FStar.Ghost
open FStar.SST
module StackHeap = FStar.StackHeap2

let lemma_uSize (x:int) (pos:nat) : Lemma (requires (UInt.size x n))
				     (ensures (x >= 0))
				     [SMTPat (UInt.size x n)]
  = ()
  
(* Buffer general type, fully implemented on FStar's arrays *)
abstract type buffer (a:Type) = {
  content:array a; 
  idx:uint32;    // JK: used machine integer so that if the code is meant to go to OCaml, that module can be extracted instead of being realized 
  length:uint32;
}

// JK: should those heap functions not be ghost ? Or returned an erased type ?
let contains #a h (b:buffer a) : GTot bool = StackHeap.contains #(bounded_seq a) h b.content
let sel #a h (b:buffer a) : GTot (seq a) = StackHeap.sel #(bounded_seq a) h b.content
let max_length #a h (b:buffer a) : GTot nat = Seq.length (sel h b)

val length: #a:Type -> b:buffer a -> GTot nat 
let length #a b = v b.length

(* let length_fail (#a:Type) (b:buffer a) : GTot nat = v b.length (\* JK: Fails to typecheck for some reason *\) *)

let length' #a (b:buffer a) : GTot uint32 = b.length
val idx: #a:Type -> b:buffer a -> GTot nat
let idx #a b = v b.idx
(* let idx #a (b:buffer a) : GTot nat = v b.idx (\* JK: idem above *\) *)
let content #a (b:buffer a) : GTot (array a) = (b.content)
let get_ref #a (b:buffer a) : GTot (Heap.ref (bounded_seq a)) = asRef (b.content)

(* Liveness condition, necessary for any computation on the buffer *)
// JK: coercion is not well enforced between booleans and Type0s
let live #a (h:mem) (b:buffer a) : GTot Type0 = 
  contains h b /\ max_length h b >= length b + idx b

let disjoint #a #a' (b:buffer a) (b':buffer a') : GTot Type0 =
  (b.content =!= b'.content
  \/ (b.content == b'.content  /\ a=a'
     /\ (idx b + length b <= idx b' \/ idx b' + length b' <= idx b)))

(* Defines that sb is a subbuffer of b *)
let subBuffer #a (sb:buffer a) (b:buffer a) : GTot Type0 =
  b.content = sb.content /\ idx sb >= idx b
  /\ idx b + length b >= idx sb + length sb

let getValue #a h (b:buffer a) (i:nat{i<max_length h b}) : GTot a = Seq.index (sel h b) i
let get #a h (b:buffer a{live h b}) (i:nat{i < length b}) : GTot a = Seq.index (sel h b) (idx b + i)

(* Equality between buffers of sints *)
let equal #a h0 (b:buffer a) h1 (c:buffer a) : GTot Type0 =
  live h0 b /\ live h1 c /\ length b = length c /\ 
  (forall (i:nat). {:pattern (get h0 b i) \/ (get h1 c i)} i < length b ==> get h0 b i = get h1 c i)

(* Abstraction of buffers of any type *)
#set-options "--__temp_no_proj SBuffer"
type abuffer = | Buff: #t:Type -> b:buffer t -> abuffer

// JK: these should be GTot, but painful in lemma calls
let empty : erased (Set.set abuffer) = hide (FStar.Set.empty #abuffer)
let only #t b : Tot (Set.set abuffer) = FStar.Set.singleton (Buff #t b)
let op_Plus_Plus #a s (b:buffer a) : Tot (Set.set abuffer) = Set.union s (only b)
let op_Plus_Plus_Plus set1 set2 : Tot (Set.set abuffer) = FStar.Set.union set1 set2

(* Maps a set of buffer to the set of their references *)
assume val arefs: FStar.Set.set abuffer -> Tot (FStar.Set.set Heap.aref)

(** TODO: make it minimal & review **)
assume Arefs1: forall (#a:Type) (b:buffer a) (s:FStar.Set.set abuffer). {:pattern (FStar.Set.mem (Heap.Ref (get_ref b)) (arefs s))}
	      FStar.Set.mem (Buff b) s ==> FStar.Set.mem (Heap.Ref (get_ref b)) (arefs s)
assume Arefs2: forall (s:FStar.Set.set abuffer) (s':FStar.Set.set abuffer). {:pattern (FStar.Set.subset s s')}
	      FStar.Set.subset s s' ==> FStar.Set.subset (arefs s) (arefs s')
assume Arefs3: arefs (reveal empty) = FStar.Set.empty #Heap.aref
assume Arefs4: forall (s1:FStar.Set.set abuffer) (s2:FStar.Set.set abuffer). {:pattern (FStar.Set.union s1 s2)}
  FStar.Set.equal (arefs (FStar.Set.union s1 s2)) (FStar.Set.union (arefs s1) (arefs s2))
assume Arefs5: forall (#a:Type) (b:buffer a). {:pattern (arefs (FStar.Set.singleton (Buff b)))}
  FStar.Set.equal (arefs (FStar.Set.singleton (Buff b))) (FStar.Set.singleton (Heap.Ref (get_ref b)))

(* Specifies that a buffer is disjoint from a set of abstract buffers *)
let disjointSet (#a:Type) (b:buffer a) (buffs:FStar.Set.set abuffer) : GTot Type0 =
  (forall (#a':Type) (b':buffer a'). {:pattern (FStar.Set.mem (Buff b') buffs) \/ (disjoint b b')} FStar.Set.mem (Buff b') buffs ==> disjoint b b')

let disjointRef #a (b:buffer a) set : GTot Type0 = ~(Set.mem (Heap.Ref (get_ref b)) set)

let modifies_buf rid buffs refs h h' = 
  modifies_ref rid  (Set.union (arefs buffs) refs) h h'
  /\ (forall (#a:Type) (b:buffer a). {:pattern (disjointSet b buffs) \/ (disjointRef b refs)}
      (live h b /\ disjointSet b buffs /\ disjointRef b refs) ==> equal h b h' b)

(** Lemmas; TODO: give better names, check triggers **)
val disjoint_only_lemma: #a:Type -> #a':Type -> b:buffer a -> b':buffer a' -> Lemma
  (requires (disjoint b b'))
  (ensures (disjointSet b (only b')))
let disjoint_only_lemma #t #t' b b' = ()  

let equal_lemma #a rid h0 h1 b bufs : 
  Lemma (requires (live h0 b /\ disjointSet b bufs /\ modifies_buf rid bufs Set.empty h0 h1))
	(ensures (equal h0 b h1 b))
	[SMTPat (disjointSet b bufs); SMTPat (modifies_buf rid bufs Set.empty h0 h1)]
 = ()

let equal_lemma_2 #a h0 h1 rid b bufs refs : 
  Lemma (requires (live h0 b /\ disjointSet b bufs /\ disjointRef b refs /\ modifies_buf rid bufs refs h0 h1))
	(ensures (equal h0 b h1 b))
	[SMTPat (equal h0 b h1 b)]
//	[SMTPat (disjointSet a bufs); SMTPat (disjointSet SMTPat (modifies bufs refs h0 h1)]
 = ()

let modifies_trans #rid bufs h0 h1 h2 :
  Lemma (requires (modifies_buf rid bufs Set.empty h0 h1 /\ modifies_buf rid bufs Set.empty h1 h2))
	(ensures (modifies_buf rid bufs Set.empty h0 h2))
	[SMTPat (modifies_buf rid bufs Set.empty h0 h1); SMTPat (modifies_buf rid bufs Set.empty h1 h2)]
 = ()

let modifies_trans_2 #rid bufs refs h0 h1 h2 :
  Lemma (requires (modifies_buf rid bufs refs h0 h1 /\ modifies_buf rid bufs refs h1 h2))
	(ensures (modifies_buf rid bufs refs h0 h2))
	[SMTPat (modifies_buf rid bufs refs h0 h1); SMTPat (modifies_buf rid bufs refs h1 h2)]
 = ()

let modifies_sub #rid bufs subbufs h0 h1 :
  Lemma 
    (requires (Set.subset subbufs bufs /\ modifies_buf rid subbufs Set.empty h0 h1))
    (ensures (modifies_buf rid bufs Set.empty h0 h1))
    [SMTPat (modifies_buf rid subbufs Set.empty h0 h1); SMTPat (Set.subset subbufs bufs)]
 = ()

let modifies_sub_2 #rid bufs subbufs refs subrefs h0 h1 :
  Lemma 
    (requires (Set.subset subbufs bufs /\ Set.subset subrefs refs /\ modifies_buf rid subbufs refs h0 h1))
    (ensures (modifies_buf rid bufs refs h0 h1))
    [SMTPat (modifies_buf rid subbufs refs h0 h1); SMTPat (Set.subset subbufs bufs); SMTPat (Set.subset subrefs refs)]
 = ()

let modifies_none h : Lemma (requires (True)) (ensures (forall i. List.Tot.contains i (frame_ids h) ==> modifies_buf i Set.empty Set.empty h h)) = ()

(* val lemma_heap: #t:Type -> r:Heap.ref t -> s:Set.set Heap.aref -> h:Heap.heap -> h':Heap.heap -> Lemma  *)
(*   (requires (Heap.modifies (Set.union s !{r}) h h' *)
(* 	     /\ not (Heap.contains h r) )) *)
(*   (ensures (Heap.modifies s h h')) *)
(* let lemma_heap #t r s h h' = () *)

let modifies_fresh #a h0 h1 bufs refs (b:buffer a) :
  Lemma
    (requires (not(contains h0 b) /\ contains h1 b
	       /\ modifies_buf (frameOf (content b)) (bufs ++ b) refs h0 h1
	       /\ frame_ids h0 = frame_ids h1))
    (ensures (modifies_buf (frameOf (content b)) bufs refs h0 h1))
    [SMTPat (not(contains h0 b)); SMTPat (modifies_buf (frameOf (content b)) (bufs ++ b) refs h0 h1)]
 = ()

(* Equality between fragments of buffers *)
let equalSub (#a:Type) (hb:mem) (b:buffer a) (b_idx:nat) (hb':mem) (b':buffer a) (b_idx':nat) (len:nat) : GTot Type0 =
  (live hb b) /\ (live hb' b') /\ (length b >= b_idx + len) /\ (length b' >= b_idx' + len)
  /\ (forall (i:nat). {:pattern (get hb b) \/ (get hb' b')} i < len ==> get hb b (b_idx+i) == get hb' b' (b_idx'+i))

(* Specifies an atomic update to a buffer *)
let atomicUpdate (#a:Type) h0 h1 (b:buffer a) (n:nat) z : GTot Type0 =
  live h0 b /\ live h1 b /\ n < length b /\ get h1 b n == z /\ max_length h1 b = max_length h0 b 
  /\ (forall (i:nat). {:pattern (get h1 b i)} (i < length b /\ i <> n) ==> get h1 b i == get h0 b i)
  /\ modifies_buf (frameOf (content b)) (only b) Set.empty h0 h1
  /\ frame_ids h0 = frame_ids h1 
  /\ modifies_one (frameOf (content b)) h0 h1
  
(** Concrete getters and setters **)

let create #a (init:a) (len:uint32) : 
  ST (buffer a)
     (requires (fun h -> True))
     (ensures (fun (h0:mem) b h1 ->
       not(contains h0 b) /\ live h1 b /\ idx b = 0 /\ length b = v len 
       /\ modifies_buf (top_frame_id h1) Set.empty Set.empty h0 h1
       /\ frame_ids h1 = frame_ids h0
       /\ modifies_one (top_frame_id h1) h0 h1
       /\ (forall (i:nat). {:pattern (get h1 b i)} i < v len ==> 
	   get h1 b i == init)))
  = let content = StackArray.create len init in 
    {content = content; idx = (uint_to_t 0); length = len}

let index #a (b:buffer a) (n:uint32{v n<length b}) : 
  STL a
     (requires (fun h -> live h b))
     (ensures (fun h0 z h1 -> live h0 b /\ (h1 == h0) /\ (z == get h0 b (v n))))
  = StackArray.index b.content (b.idx+^n)

let lemma_aux_0 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') : Lemma
  (requires (True))
  (ensures (frameOf (content b) <> frameOf (content b') ==> content b' =!= content b))
  [SMTPat (frameOf (content b) <> frameOf (content b'))]
  = ()

(* JK: Breaks extraction for some reason *)
let lemma_aux (#a:Type) (#a':Type) (b:buffer a) (h0:t) (h1:t) (b':buffer a') : Lemma
  (requires (live h0 b /\ live h0 b'
	     /\ frame_ids h0 = frame_ids h1
	     /\ modifies_one (frameOf (content b)) h0 h1
	     /\ modifies_ref (frameOf (content b)) !{as_ref (content b)} h0 h1
	     /\ (content b' =!= content b \/ a <> a')))
  (ensures (equal h0 b' h1 b'))
  [SMTPat (equal h0 b' h1 b')]
  = 
    admit()
    (* if frameOf (content b) <> frameOf (content b') then () *)
    (* else if a <> a' then () *)
    (* else if a = a' && content b <> content b' then () *)

let upd #a (b:buffer a) (n:uint32{v n < length b}) z :
  STL unit
     (requires (fun h -> live h b))
     (ensures (fun h0 _ h1 -> atomicUpdate #a h0 h1 b (v n) z))
  = let h0 = SST.get () in
    StackArray.upd b.content (b.idx +^ n) z;
    let h1 = SST.get () in
    cut (Set.mem (Buff b) (only b));
    cut (modifies_one (frameOf (content b)) h0 h1);
    ()

let sub #a (b:buffer a) (i:uint32) (len:uint32{v len <= length b /\ v i + v len <= length b}) :
  STL (buffer a)
     (requires (fun h -> live h b))
     (ensures (fun h0 b' h1 -> content b = content b' /\ idx b' = idx b + v i /\ length b' = v len /\ (h0 == h1)))
  = {content = b.content; idx = i +^ b.idx; length = len}

let lemma_modifies_one_trans_1 (#a:Type) (b:buffer a) (h0:t) (h1:t) (h2:t): Lemma
  (requires (modifies_one (frameOf (content b)) h0 h1 /\ modifies_one (frameOf (content b)) h1 h2))
  (ensures (modifies_one (frameOf (content b)) h0 h2))
  [SMTPat (modifies_one (frameOf (content b)) h0 h1); SMTPat (modifies_one (frameOf (content b)) h1 h2)]
  = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // TODO: remove 

(* TODO: simplify, add triggers ? *)
private val blit_aux: #a:Type -> b:buffer a -> idx_b:uint32{v idx_b<=length b} -> 
				 b':buffer a{disjoint b b'} -> idx_b':uint32{v idx_b'<=length b'} -> 
				 len:uint32{v idx_b+v len <= length b /\ v idx_b'+v len <= length b'} -> 
				 ctr:uint32{v ctr<=v len} ->  STL unit
  (requires (fun h -> live h b /\ live h b' /\ length b >= v idx_b + v len /\ length b' >= v idx_b' + v len
		    /\ (forall (i:nat). i < v ctr ==> get h b (v idx_b+i) = get h b' (v idx_b'+i)) ))
  (ensures (fun h0 _ h1 -> live h1 b /\ live h1 b' 
			 /\ live h0 b /\ live h0 b' 
			 /\ length b >= v idx_b+v len /\ length b' >= v idx_b'+v len
			 /\ (forall (i:nat). {:pattern (get h1 b' (v idx_b'+i))} i < v len ==> get h0 b (v idx_b+i) = get h1 b' (v idx_b'+i))
			 /\ (forall (i:nat). {:pattern (get h1 b' i)} (i < v idx_b' \/ (i >= v idx_b'+v len /\ i < length b')) 
			     ==> get h1 b' i = get h0 b' i)
			 /\ frame_ids h1 = frame_ids h0
			 /\ modifies_one (frameOf (content b')) h0 h1
			 /\ modifies_buf (frameOf (content b')) (only b') Set.empty h0 h1 ))
let rec blit_aux #a b idx_b b' idx_b' len ctr = 
  let h0 = SST.get() in
  if (len -^ ctr) =^ (uint_to_t 0) then ()
  else 
  begin
    let bctr = index b (idx_b +^ ctr) in
    upd b' (idx_b' +^ ctr) bctr;
    let h1 = SST.get() in
    // JK: required for verfication but breaks extraction (infinite loop)
    (* equal_lemma (frameOf (content b')) h0 h1 b (only b'); *)
    cut (forall (i:nat). {:pattern (get h1 b' i)} (i <> v idx_b'+v ctr /\ i < length b') ==> get h1 b' i = get h0 b' i);
    cut (modifies_one (frameOf (content b')) h0 h1);
    cut (modifies_buf (frameOf (content b')) (only b') Set.empty h0 h1);
    blit_aux b idx_b b' idx_b' len (ctr +^ (uint_to_t 1));
    let h2 = SST.get() in
    // JK: required for verfication but breaks extraction (infinite loop)
    (* equal_lemma (frameOf (content b')) h1 h2 b (only b'); *)
    cut (live h2 b /\ live h2 b');
    cut (forall (i:nat). {:pattern (get h2 b')} i < v len ==> get h2 b' (v idx_b'+i) = get h1 b (v idx_b+i));
    cut (forall (i:nat). {:pattern (get h2 b')} i < v len ==> get h2 b' (v idx_b'+i) = get h0 b (v idx_b+i));
    cut (forall (i:nat). {:pattern (get h2 b')} (i < v idx_b' \/ (i >= v idx_b'+v len /\ i < length b')) ==> get h2 b' i = get h1 b' i);
    cut (modifies_one (frameOf (content b')) h1 h2);
    cut (modifies_buf (frameOf (content b')) (only b') Set.empty h1 h2);
    cut (modifies_one (frameOf (content b')) h0 h2);
    cut (modifies_buf (frameOf (content b')) (only b') Set.empty h0 h2);
    cut (modifies_ref (frameOf (content b')) !{as_ref (content b')} h0 h1); (* Trigger *)
    cut (modifies_ref (frameOf (content b')) !{as_ref (content b')} h1 h2); (* Trigger *)
    cut (modifies_ref (frameOf (content b')) !{as_ref (content b')} h0 h2) (* Trigger *)
  end

#reset-options

val blit: #t:Type -> a:buffer t -> idx_a:uint32{v idx_a <= length a} -> b:buffer t{disjoint a b} -> 
  idx_b:uint32{v idx_b <= length b} -> len:uint32{v idx_a+v len <= length a /\ v idx_b+v len <= length b} -> STL unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 a /\ live h1 b /\ live h1 a
      /\ (forall (i:nat). {:pattern (get h1 b (v idx_b+i))} i < v len ==> get h1 b (v idx_b+i) = get h0 a (v idx_a+i))
      /\ (forall (i:nat). {:pattern (get h1 b i)} ((i >= v idx_b + v len /\ i < length b) \/ i < v idx_b) ==> get h1 b i = get h0 b i)
      /\ modifies_one (frameOf (content b)) h0 h1
      /\ modifies_buf (frameOf (content b)) (only b) Set.empty h0 h1
      /\ frame_ids h0 = frame_ids h1
      ))
let blit #t a idx_a b idx_b len = 
  blit_aux a idx_a b idx_b len (uint_to_t 0)

val split: #a:Type -> a:buffer t -> i:uint32{v i <= length a} -> ST (buffer t * buffer t)
    (requires (fun h -> live h a))
    (ensures (fun h0 b h1 -> live h1 (fst b) /\ live h1 (snd b) /\ h1 == h0 /\ idx (fst b) = idx a 
      /\ idx (snd b) = idx a + v i /\ length (fst b) = v i /\ length (snd b) = length a - v i 
      /\ disjoint (fst b) (snd b)  /\ content (fst b) = content a /\ content (snd b) = content a))
let split #t a i = 
  let a1 = sub a (uint_to_t 0) i in let a2 = sub a i (a.length -^ i) in a1, a2

val offset: #a:Type -> a:buffer t -> i:uint32{v i <= length a} -> STL (buffer t)
  (requires (fun h -> live h a))
  (ensures (fun h0 a' h1 -> h0 == h1 /\ content a' = content a /\ idx a' = idx a + v i /\ length a' = length a - v i))
let offset #t a i = 
  {content = a.content; idx = i +^ a.idx; length = a.length -^ i}

private val of_seq_aux: #a:Type -> s:bounded_seq a -> l:uint32{v l = Seq.length s} -> ctr:uint32{v ctr <= v l} -> b:buffer a{idx b = 0 /\ length b = v l} -> STL unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b 
      /\ (forall (i:nat). {:pattern (get h1 b i)} i < v ctr ==> get h1 b i = Seq.index s i)
      /\ (forall (i:nat). {:pattern (get h1 b i)} i >= v ctr /\ i < length b ==> get h1 b i = get h0 b i)
      /\ frame_ids h0 = frame_ids h1
      /\ modifies_one (frameOf (content b)) h0 h1
      /\ modifies_buf (frameOf (content b)) (only b) Set.empty h0 h1))
let rec of_seq_aux #a s l ctr b =
  if ctr =^ (uint_to_t 0) then ()
  else 
  begin
    let j = ctr -^ (uint_to_t 1) in 
    upd b j (Seq.index s (v j)); (* JK: no concrete implementation of Seq for now as far as I know *)
    of_seq_aux s l j b	 
  end

val of_seq: #a:Type -> s:seq a -> l:uint32{v l = Seq.length s /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> True))
  (ensures (fun h0 b h1 -> idx b = 0 /\ length b = v l /\ not(contains h0 b) /\ live h1 b
    /\ (forall (i:nat). {:pattern (get h1 b i)} i < v l ==> get h1 b i = Seq.index s i)
    /\ frame_ids h0 = frame_ids h1
    /\ modifies_one (frameOf (content b)) h0 h1
    /\ modifies_buf (frameOf (content b)) (only b) Set.empty h0 h1))
let of_seq #a s l =
  let init = Seq.index s 0 in
  let b = create #a init l in 
  of_seq_aux s l l b; 
  b

val clone: #a:Type ->  b:buffer a -> l:uint32{length b >= v l /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> not(contains h0 b')
	      /\ live h0 b
	      /\ live h1 b'
	      /\ idx b' = 0 
	      /\ length b' = v l 
	      /\ (forall (i:nat). {:pattern (get h1 b' i)} i < v l ==> get h1 b' i = get h0 b i)
	      /\ modifies_one (frameOf (content b')) h0 h1
	      /\ modifies_buf (frameOf (content b')) Set.empty Set.empty h0 h1
	      /\ frame_ids h0 = frame_ids h1))
let clone #a b l =
  let (init:a) = index b (uint_to_t 0) in 
  let (b':buffer a) = create init l in 
  blit b (uint_to_t 0) b' (uint_to_t 0) l; 
  b'
