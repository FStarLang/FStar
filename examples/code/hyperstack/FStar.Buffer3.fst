module FStar.Buffer3

open FStar.Seq
open FStar.UInt32
open FStar.HyperStack
open FStar.StackArray
open FStar.Ghost
open FStar.HST

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let u32 = UInt32.t

let lemma_size (x:int) (pos:nat) : Lemma (requires (UInt.size x n))
				     (ensures (x >= 0))
				     [SMTPatT (UInt.size x n)]
  = ()

(* Buffer general type, fully implemented on FStar's arrays *)
private type buffer' (a:Type) = {
  content:array a; 
  idx:u32;    // JK: used machine integer so that if the code is meant to go to OCaml, that module can be extracted instead of being realized 
  length:u32;
}
type buffer (a:Type) = buffer' a

// JK: should those heap functions not be ghost ? Or returned an erased type ?
let contains #a h (b:buffer a) : GTot Type0 = HS.contains #(bounded_seq a) h b.content
let sel #a h (b:buffer a{contains h b}) : GTot (seq a) = HS.sel #(bounded_seq a) h b.content
let max_length #a h (b:buffer a{contains h b}) : GTot nat = Seq.length (sel h b)
let length #a (b:buffer a) : GTot nat = v b.length
let length' #a (b:buffer a) : GTot u32 = b.length
let idx #a (b:buffer a) : GTot nat = v b.idx
let content #a (b:buffer a) : GTot (array a) = b.content
let as_ref #a (b:buffer a) : GTot (Heap.ref (bounded_seq a)) = as_ref (b.content)
let as_aref #a (b:buffer a) : GTot Heap.aref = as_aref b.content
let frameOf #a (b:buffer a) : GTot HH.rid = frameOf (content b)

(* Liveness condition, necessary for any computation on the buffer *)
// JK: coercion is not well enforced between booleans and Type0s
let live #a (h:mem) (b:buffer a) : GTot Type0 = 
  contains h b /\ max_length h b >= length b + idx b

let getValue #a h (b:buffer a{live h b}) (i:nat{i<max_length h b}) : GTot a = Seq.index (sel h b) i
let get #a h (b:buffer a{live h b}) (i:nat{i < length b}) : GTot a = Seq.index (sel h b) (idx b + i)
let as_seq #a h (b:buffer a{live h b}) : GTot (seq a) = Seq.slice (sel h b) (idx b) (idx b + length b)
let equal #a h (b:buffer a) h' (b':buffer a) : GTot Type0 =
  live h b /\ live h' b' /\ Seq.equal (as_seq h b) (as_seq h' b')

(* y is included in x / x contains y *)
let includes #a (x:buffer a) (y:buffer a) : GTot Type0 =
  x.content = y.content /\ idx y >= idx x /\ idx x + length x >= idx y + length y

let disjoint #a #a' (x:buffer a) (y:buffer a') : GTot Type0 =
  as_aref x <> as_aref y
  \/ (as_aref x = as_aref y /\ (idx x + length x <= idx y \/ idx y + length y <= idx x))

(* Abstraction of buffers of any type *)
#set-options "--__temp_no_proj SBuffer"
type asref = | Buf: #a:Type -> b:buffer a -> asref
	     | Ref: #a:Type -> r:stackref a -> asref

let rid_of (a:asref) : GTot HH.rid = match a with | Buf b -> frameOf b
						  | Ref r -> r.id

let aref_of (a:asref) : GTot Heap.aref = match a with | Buf b -> as_aref b
						      | Ref r -> HS.as_aref r

let disj (a:asref) (b:asref) : GTot Type0 =
  rid_of a <> rid_of b \/ aref_of a <> aref_of b
  \/ (rid_of a = rid_of b /\ aref_of a = aref_of b /\ is_Buf a /\ is_Buf b
      /\ (match a, b with
	| Buf #ta a, Buf #tb b -> idx (b) + length (b) <= idx (a) \/ idx (a) + length (a) <= idx (b)) )

let empty : Set.set asref = Set.empty #asref
let only #t (b:buffer t) : Tot (Set.set asref) = FStar.Set.singleton (Buf #t b)
let op_Plus_Plus #a s (b:buffer a) : Tot (Set.set asref) = Set.union s (only b)
let op_Plus_Plus_Plus set1 set2 : Tot (Set.set asref) = FStar.Set.union set1 set2

(* Maps a set of buffer to the set of their references *)
assume val arefs: Set.set asref -> Tot (Set.set Heap.aref)

assume Arefs1: arefs (Set.empty) = Set.empty
assume Arefs2: forall (#a:Type) (s:Set.set asref) (b:buffer a).
  Set.equal (arefs (Set.union s (Set.singleton (Buf b))))
	    (Set.union (arefs s) (Set.singleton (as_aref b)))
assume Arefs3: forall (s1:Set.set asref) (s2:Set.set asref).
  Set.equal (arefs (Set.union s1 s2)) (Set.union (arefs s1) (arefs s2))
assume Arefs4: forall (s1:Set.set asref) (s2:Set.set asref).
  Set.subset s1 s2 ==> Set.subset (arefs s1) (arefs s2)

let disjointSet b (refs:Set.set asref) = (forall b'. Set.mem b' refs ==> disj b b')

(* Probably not good *)
let eq ha (a:asref) hb (b:asref) : GTot Type0 = 
  match a, b with
  | Buf #ta a', Buf #tb b' -> ta = tb /\ equal ha a' hb b'
  | Buf #ta a', Ref #tb b' -> bounded_seq ta = tb /\ b2t(HS.sel ha (content a') = HS.sel hb b')
  | Ref #ta a', Buf #tb b' -> bounded_seq tb = ta /\ b2t(HS.sel ha a' = HS.sel hb (content b'))
  | Ref #ta a', Ref #tb b' -> ta = tb /\ b2t(HS.sel ha a' = HS.sel hb b')

assume val rids_of: s:Set.set asref -> Tot (Set.set HH.rid)

assume Rids_of: forall s r. Set.mem r s ==> Set.mem (rid_of r) (rids_of s)
// TODO: add other specs

let modifies (s:Set.set asref) h h' =
  HS.modifies (rids_of s) h h'
  /\ (forall r. Set.mem r s ==> HH.modifies_rref (rid_of r) (arefs s) h.h h'.h)
  /\ (forall r'. disjointSet r' s ==> eq h r' h' r')

val disjoint_only_lemma: b:asref -> b':asref -> Lemma
  (requires (disj b b'))
  (ensures (disjointSet b (Set.singleton b')))
  [SMTPat (disjointSet b (Set.singleton b'))]
let disjoint_only_lemma b b' = ()

let equal_lemma h0 h1 b bufs :
  Lemma (requires (live h0 (Buf.b b) /\ disjointSet b bufs /\ modifies bufs h0 h1))
	(ensures (eq h0 b h1 b))
	[SMTPatT (disjointSet b bufs); SMTPatT (modifies bufs h0 h1)]
 = ()

let modifies_trans #rid bufs h0 h1 h2 :
  Lemma (requires (modifies bufs h0 h1 /\ modifies bufs h1 h2))
	(ensures (modifies bufs h0 h2))
	[SMTPatT (modifies bufs h0 h1); SMTPatT (modifies bufs h1 h2)]
 = ()

let modifies_sub bufs subbufs h0 h1 :
  Lemma
    (requires (Set.subset subbufs bufs /\ modifies subbufs h0 h1))
    (ensures (modifies bufs h0 h1))
    [SMTPatT (modifies subbufs h0 h1); SMTPat (Set.subset subbufs bufs)]
 =  admit() // TODO

let modifies_none h : Lemma (modifies Set.empty h h) = admit() // TODO

val lemma_aux_0: #a:Type -> #a':Type -> h0:mem -> h1:mem -> bufs:Set.set asref -> b:buffer a -> b':buffer a' -> Lemma
  (requires (~(live h0 b') /\ live h0 b /\ disjointSet (Buf b) (bufs++b') ))
  (ensures (disjointSet (Buf b) bufs))
  [SMTPat (modifies (bufs++b') h0 h1); SMTPat (live h0 b)]
let lemma_aux_0 #a #a' h0 h1 bufs b b' = ()

val lemma_aux_3: #a:Type -> #a':Type -> h:Heap.heap -> b:Heap.ref a -> b':Heap.ref a' -> Lemma
  (requires (Heap.contains h b /\ ~(Heap.contains h b')))
  (ensures (Heap.Ref b <> Heap.Ref b'))
let lemma_aux_3 #a #a' h b b' = ()

val lemma_aux_2: #a:Type -> #a':Type -> h:mem -> b:buffer a -> b':buffer a' -> Lemma
  (requires (live h b /\ ~(contains h b')))
  (ensures (disjoint b b'))
  [SMTPatT (disjoint b b')]
let lemma_aux_2 #a #a' h b b' = lemma_live_1 h (content b) (content b')

val lemma_aux_1: #a:Type -> #a':Type -> h0:mem -> h1:mem -> bufs:Set.set asref -> refs:Set.set Heap.aref -> b:buffer a -> b':buffer a' -> Lemma
  (requires (~(contains h0 b') /\ live h0 b /\ disjointSet (Buf b) bufs))
  (ensures (disjointSet (Buf b) (bufs++b')))
  [SMTPat (modifies bufs h0 h1); SMTPat (~(live h0 b')); SMTPat (live h0 b)]
let lemma_aux_1 #a #a' h0 h1 bufs refs b b' = ()

val modifies_fresh: #a:Type -> h0:mem -> h1:mem -> bufs:Set.set asref -> refs:Set.set Heap.aref -> b:buffer a -> Lemma
  (requires (~(contains h0 b) /\ contains h1 b /\ frameOf b = h0.tip
    /\ modifies (bufs ++ b) h0 h1))
  (ensures (~(contains h0 b) /\ contains h1 b /\ frameOf b = h0.tip
    /\ modifies bufs h0 h1 ))
let modifies_fresh #a h0 h1 bufs refs b = admit() // TODO

(*

(** Concrete getters and setters **)
let create #a (init:a) (len:u32) : ST (buffer a)
     (requires (fun h -> True))
     (ensures (fun (h0:mem) b h1 -> ~(contains h0 b) /\ live h1 b /\ idx b = 0 /\ length b = v len 
       (* /\ modifies_one h1.tip h0 h1 *)
       /\ modifies Set.empty h0 h1
       /\ (forall (i:nat). {:pattern (get h1 b i)} i < v len ==> get h1 b i == init)))
  = let content = StackArray.create len init in 
    {content = content; idx = (uint_to_t 0); length = len}

let index #a (b:buffer a) (n:u32{v n<length b}) : STL a
     (requires (fun h -> live h b))
     (ensures (fun h0 z h1 -> live h0 b /\ (h1 == h0) /\ (z == get h0 b (v n))))
  = StackArray.index b.content (b.idx+^n)

(* let lemma_aux_4 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') : Lemma *)
(*   (requires (True)) *)
(*   (ensures (frameOf b <> frameOf b' ==> content b' =!= content b)) *)
(*   [SMTPat (frameOf b <> frameOf (b'))] *)
(*   = () *)

(* JK: Breaks extraction for some reason *)
let lemma_aux_5 (#a:Type) (#a':Type) (b:buffer a) (h0:mem) (h1:mem) (b':buffer a') : Lemma
  (requires (live h0 b /\ live h0 b'
	     /\ modifies_one (frameOf b) h0 h1
	     /\ modifies_ref (frameOf b) !{as_ref b} h0 h1
	     /\ as_aref b <> as_aref b'))
  (ensures (equal h0 b' h1 b'))
  [SMTPat (equal h0 b' h1 b')]
  = ()

(* val lemma_aux_7: #a:Type -> #a':Type -> b:buffer a -> b':buffer a' -> h:heap -> Lemma *)
(*   (requires (live h b /\ live h b' /\ disjointSet b' (only b) *)

let lemma_aux_7 (#a:Type) (b:buffer a) : Lemma
  (requires (True))
  (ensures  (Set.equal (arefs (only b)) (Set.singleton (as_aref b))))
  [SMTPat (arefs (only b))]
  = cut (Set.equal (Set.union Set.empty (arefs (only b))) (arefs (only b)))

let lemma_aux_6 #a (b:buffer a) (n:u32{v n < length b}) (z:a) h0 : Lemma
  (requires (live h0 b))
  (ensures (live h0 b 
    /\ modifies_one (frameOf b) h0 (HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z))
    /\ modifies_buf (frameOf b) (only b) Set.empty h0 (HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z))))
  [SMTPat (HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z))]
  = let h1 = HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z) in
    assume (forall (#a':Type) (b':buffer a'). (live h0 b' /\ disjointSet b' (only b) /\ disjointRef b' Set.empty) ==> equal h0 b' h1 b')

val upd: #a:Type -> b:buffer a -> n:u32 -> z:a -> STL unit
  (requires (fun h -> live h b /\ v n < length b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ v n < length b
    /\ modifies_one (frameOf b) h0 h1
    /\ modifies_buf (frameOf b) (only b) Set.empty h0 h1
    /\ sel h1 b = Seq.upd (sel h0 b) (idx b + v n) z))
let upd #a b n z = StackArray.upd b.content (b.idx +^ n) z

let sub #a (b:buffer a) (i:u32) (len:u32{v len <= length b /\ v i + v len <= length b}) : STL (buffer a)
     (requires (fun h -> live h b))
     (ensures (fun h0 b' h1 -> content b = content b' /\ idx b' = idx b + v i /\ length b' = v len /\ (h0 == h1)))
  = {content = b.content; idx = i +^ b.idx; length = len}

let lemma_modifies_one_trans_1 (#a:Type) (b:buffer a) (h0:mem) (h1:mem) (h2:mem): Lemma
  (requires (modifies_one (frameOf b) h0 h1 /\ modifies_one (frameOf b) h1 h2))
  (ensures (modifies_one (frameOf b) h0 h2))
  [SMTPat (modifies_one (frameOf b) h0 h1); SMTPat (modifies_one (frameOf b) h1 h2)]
  = ()

#reset-options "--z3timeout 100"
(* #set-options "--lax" // TODO: remove *)

(* TODO: simplify, add triggers ? *)
private val blit_aux: #a:Type -> b:buffer a -> idx_b:u32 -> 
  b':buffer a -> idx_b':u32 -> len:u32{v idx_b+v len<=length b/\v idx_b'+v len<= length b'} -> 
  ctr:u32{v ctr <= v len} ->  STL unit
  (requires (fun h -> live h b /\ live h b'
    /\ disjoint b b'
    /\ (forall (i:nat). i < v ctr ==> get h b (v idx_b+i) = get h b' (v idx_b'+i)) ))
  (ensures (fun h0 _ h1 -> live h1 b /\ live h1 b'  /\ live h0 b /\ live h0 b' 
    /\ disjoint b b'
    /\ length b >= v idx_b+v len /\ length b' >= v idx_b'+v len
    /\ modifies_one (frameOf b') h0 h1
    /\ modifies_buf (frameOf b') (only b') Set.empty h0 h1    
    /\ (forall (i:nat). {:pattern (get h1 b' (v idx_b'+i))} i < v len 
	==> get h0 b (v idx_b+i) = get h1 b' (v idx_b'+i))
    /\ (forall (i:nat). {:pattern (get h1 b' i)} (i < v idx_b' \/ (i >= v idx_b'+v len /\ i < length b')) 
	==> get h1 b' i = get h0 b' i) ))
let rec blit_aux #a b idx_b b' idx_b' len ctr = 
  let h0 = HST.get() in
  if (len -^ ctr) =^ (uint_to_t 0) then ()
  else
  begin
    let bctr = index b (idx_b +^ ctr) in
    upd b' (idx_b' +^ ctr) bctr;
    let h1 = HST.get() in
    // JK: required for verfication but breaks extraction (infinite loop)
    (* equal_lemma (frameOf b') h0 h1 b (only b'); *)
    cut (forall (i:nat). {:pattern (get h1 b' i)} (i <> v idx_b'+v ctr /\ i < length b') ==> get h1 b' i = get h0 b' i); 
    cut (modifies_one (frameOf b') h0 h1);
    cut (modifies_buf (frameOf b') (only b') Set.empty h0 h1);
    blit_aux b idx_b b' idx_b' len (ctr +^ (uint_to_t 1)); 
    let h2 = HST.get() in
    // JK: required for verfication but breaks extraction (infinite loop)
    (* equal_lemma (frameOf b') h1 h2 b (only b'); *)
    cut (live h2 b /\ live h2 b');
    cut (forall (i:nat). {:pattern (get h2 b')} i < v len ==> get h2 b' (v idx_b'+i) = get h1 b (v idx_b+i));
    cut (forall (i:nat). {:pattern (get h2 b')} i < v len ==> get h2 b' (v idx_b'+i) = get h0 b (v idx_b+i));
    cut (forall (i:nat). {:pattern (get h2 b')} (i < v idx_b' \/ (i >= v idx_b'+v len /\ i < length b')) ==> get h2 b' i = get h1 b' i);
    cut (modifies_one (frameOf b') h1 h2);
    cut (modifies_buf (frameOf b') (only b') Set.empty h1 h2);
    cut (modifies_one (frameOf b') h0 h2);
    cut (modifies_buf (frameOf b') (only b') Set.empty h0 h2);
    cut (modifies_ref (frameOf b') !{as_ref b'} h0 h1); (* Trigger *)
    cut (modifies_ref (frameOf b') !{as_ref b'} h1 h2); (* Trigger *)
    cut (modifies_ref (frameOf b') !{as_ref b'} h0 h2) (* Trigger *)
  end

#reset-options

val blit: #t:Type -> a:buffer t -> idx_a:u32{v idx_a <= length a} -> b:buffer t{disjoint a b} -> 
  idx_b:u32{v idx_b <= length b} -> len:u32{v idx_a+v len <= length a /\ v idx_b+v len <= length b} -> STL unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 a /\ live h1 b /\ live h1 a
      /\ (forall (i:nat). {:pattern (get h1 b (v idx_b+i))} i < v len ==> get h1 b (v idx_b+i) = get h0 a (v idx_a+i))
      /\ (forall (i:nat). {:pattern (get h1 b i)} ((i >= v idx_b + v len /\ i < length b) \/ i < v idx_b) ==> get h1 b i = get h0 b i)
      /\ modifies_one (frameOf b) h0 h1
      /\ modifies_buf (frameOf b) (only b) Set.empty h0 h1 ))
let blit #t a idx_a b idx_b len = blit_aux a idx_a b idx_b len (uint_to_t 0)

val split: #a:Type -> a:buffer t -> i:u32{v i <= length a} -> ST (buffer t * buffer t)
    (requires (fun h -> live h a))
    (ensures (fun h0 b h1 -> live h1 (fst b) /\ live h1 (snd b) /\ h1 == h0 /\ idx (fst b) = idx a 
      /\ idx (snd b) = idx a + v i /\ length (fst b) = v i /\ length (snd b) = length a - v i 
      /\ disjoint (fst b) (snd b)  /\ content (fst b) = content a /\ content (snd b) = content a))
let split #t a i = 
  let a1 = sub a (uint_to_t 0) i in let a2 = sub a i (a.length -^ i) in a1, a2

val offset: #a:Type -> a:buffer t -> i:u32{v i <= length a} -> STL (buffer t)
  (requires (fun h -> live h a))
  (ensures (fun h0 a' h1 -> h0 == h1 /\ content a' = content a /\ idx a' = idx a + v i /\ length a' = length a - v i))
let offset #t a i = {content = a.content; idx = i +^ a.idx; length = a.length -^ i}

private val of_seq_aux: #a:Type -> s:bounded_seq a -> l:u32{v l = Seq.length s} -> ctr:u32{v ctr <= v l} -> b:buffer a{idx b = 0 /\ length b = v l} -> STL unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b 
      /\ (forall (i:nat). {:pattern (get h1 b i)} i < v ctr ==> get h1 b i = Seq.index s i)
      /\ (forall (i:nat). {:pattern (get h1 b i)} i >= v ctr /\ i < length b ==> get h1 b i = get h0 b i)
      /\ modifies_one (frameOf b) h0 h1
      /\ modifies_buf (frameOf b) (only b) Set.empty h0 h1))
let rec of_seq_aux #a s l ctr b =
  if ctr =^ (uint_to_t 0) then ()
  else 
  begin
    let j = ctr -^ (uint_to_t 1) in 
    upd b j (Seq.index s (v j)); (* JK: no concrete implementation of Seq for now as far as I know *)
    of_seq_aux s l j b	 
  end

val of_seq: #a:Type -> s:seq a -> l:u32{v l = Seq.length s /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> True))
  (ensures (fun h0 b h1 -> idx b = 0 /\ length b = v l /\ ~(contains h0 b) /\ live h1 b
    /\ frameOf b = h1.tip
    /\ modifies_one (frameOf b) h0 h1
    /\ modifies_buf (frameOf b) Set.empty Set.empty h0 h1
    /\ (forall (i:nat). {:pattern (get h1 b i)} i < v l ==> get h1 b i = Seq.index s i) ))
let of_seq #a s l =
  let init = Seq.index s 0 in
  let h0 = HST.get () in
  let b = create #a init l in 
  let h1 = HST.get () in
  of_seq_aux s l l b; 
  let h2 = HST.get () in
  b

val clone: #a:Type ->  b:buffer a -> l:u32{length b >= v l /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> ~(contains h0 b')
	      /\ live h0 b
	      /\ live h1 b'
	      /\ idx b' = 0 
	      /\ length b' = v l 
	      /\ (forall (i:nat). {:pattern (get h1 b' i)} i < v l ==> get h1 b' i = get h0 b i)
	      /\ modifies_one (frameOf b') h0 h1
	      /\ modifies_buf (frameOf b') Set.empty Set.empty h0 h1 ))
let clone #a b l =
  let (init:a) = index b (uint_to_t 0) in 
  let (b':buffer a) = create init l in 
  blit b (uint_to_t 0) b' (uint_to_t 0) l; 
  b'
