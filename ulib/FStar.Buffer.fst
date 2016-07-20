module FStar.Buffer

open FStar.Seq
open FStar.UInt32
open FStar.HyperStack
open FStar.Ghost
open FStar.HST

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let lemma_size (x:int) : Lemma (requires (UInt.size x n))
				     (ensures (x >= 0))
				     [SMTPat (UInt.size x n)]
  = ()

type bounded_seq (t:Type) = s:seq t{length s <= UInt.max_int n}

(* Buffer general type, fully implemented on FStar's arrays *)
noeq private type buffer' (a:Type) = {
  content:stackref (bounded_seq a); 
  idx:UInt32.t;    // JK: used machine integer so that if the code is meant to go to OCaml, that module can be extracted instead of being realized 
  length:UInt32.t;
}
type buffer (a:Type) = buffer' a

// JK: should those heap functions not be ghost ? Or returned an erased type ?
let contains #a h (b:buffer a) : GTot Type0 = HS.contains #(bounded_seq a) h b.content
let sel #a h (b:buffer a{contains h b}) : GTot (seq a) = HS.sel #(bounded_seq a) h b.content
let max_length #a h (b:buffer a{contains h b}) : GTot nat = Seq.length (sel h b)
let length #a (b:buffer a) : GTot nat = v b.length
let length' #a (b:buffer a) : GTot UInt32.t = b.length
let idx #a (b:buffer a) : GTot nat = v b.idx
let content #a (b:buffer a) : GTot (stackref (bounded_seq a)) = b.content
let as_ref #a (b:buffer a) : GTot (Heap.ref (bounded_seq a)) = as_ref (b.content)
let as_aref #a (b:buffer a) : GTot Heap.aref = as_aref b.content
let frameOf #a (b:buffer a) : GTot HH.rid = frameOf (content b)

(* Liveness condition, necessary for any computation on the buffer *)
(* abstract *) let live #a (h:mem) (b:buffer a) : GTot Type0 = 
  contains h b /\ max_length h b >= length b + idx b

let getValue #a h (b:buffer a{live h b}) (i:nat{i<max_length h b}) : GTot a = Seq.index (sel h b) i
let get #a h (b:buffer a{live h b}) (i:nat{i < length b}) : GTot a = Seq.index (sel h b) (idx b + i)
let as_seq #a h (b:buffer a{live h b}) : GTot (seq a) = Seq.slice (sel h b) (idx b) (idx b + length b)

(* Equality predicate between buffers without existential quantifiers *)
let equal #a h (b:buffer a) h' (b':buffer a) : GTot Type0 =
  live h b /\ live h' b' /\ as_seq h b == as_seq h' b'

(* Equality predicate between buffers wih existential quantifiers *)
val eq_lemma: #a:Type -> h:mem -> b:buffer a{live h b} -> h':mem -> b':buffer a{live h' b'} -> Lemma
  (requires (equal h b h' b'))
  (ensures  (length b = length b' /\ (forall (i:nat). i < length b ==> get h b i == get h' b' i)))
  [SMTPat (equal h b h' b')]
let eq_lemma #a h b h' b' =
  let s = as_seq h b in
  let s' = as_seq h' b' in
  assert(Seq.length s = length b);
  assert(Seq.length s' = length b');
  assert(Seq.equal s s');
  assert (forall (i:nat). i < length b ==> get h b i == Seq.index s i); 
  assert (forall (i:nat). i < length b' ==> get h' b' i == Seq.index s' i)

(* y is included in x / x contains y *)
let includes #a (x:buffer a) (y:buffer a) : GTot Type0 =
  x.content == y.content /\ idx y >= idx x /\ idx x + length x >= idx y + length y

(* Disjointness between two buffers *)
let disjoint #a #a' (x:buffer a) (y:buffer a') : GTot Type0 =
  frameOf x <> frameOf y \/ as_aref x =!= as_aref y
  \/ (as_aref x == as_aref y /\ frameOf x = frameOf y /\ (idx x + length x <= idx y \/ idx y + length y <= idx x))

let lemma_disjoint_refl #a #a' (x:buffer a) (y:buffer a') : Lemma
  (requires (True))
  (ensures (disjoint x y <==> disjoint y x))
  [SMTPat (disjoint x y)]
  = ()

let lemma_disjoint_sub #a #a' (x:buffer a) (subx:buffer a) (y:buffer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPat (disjoint subx y); SMTPat (includes x subx)]
  = ()

let lemma_disjoint_sub' #a #a' (x:buffer a) (subx:buffer a) (y:buffer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPat (disjoint y subx); SMTPat (includes x subx)]
  = ()

(* (* Abstract *)ion of buffers of any type *)
#set-options "--__temp_no_proj SBuffer"
noeq type abuffer = | Buff: #t:Type -> b:buffer t -> abuffer

// JK: these should be GTot, but painful in lemma calls
let empty : TSet.set abuffer = TSet.empty #abuffer
let only #t (b:buffer t) : Tot (TSet.set abuffer) = FStar.TSet.singleton (Buff #t b)
let op_Plus_Plus #a s (b:buffer a) : Tot (TSet.set abuffer) = TSet.union s (only b)
let op_Plus_Plus_Plus set1 set2 : Tot (TSet.set abuffer) = FStar.TSet.union set1 set2

(* Maps a set of buffer to the set of their references *)
assume val arefs: TSet.set abuffer -> Tot (TSet.set Heap.aref)

assume Arefs1: arefs (TSet.empty) == TSet.empty
assume Arefs2: forall (#a:Type) (s:TSet.set abuffer) (b:buffer a).
  TSet.equal (arefs (TSet.union s (TSet.singleton (Buff b))))
	    (TSet.union (arefs s) (TSet.singleton (as_aref b)))
assume Arefs3: forall (s1:TSet.set abuffer) (s2:TSet.set abuffer).
  TSet.equal (arefs (TSet.union s1 s2)) (TSet.union (arefs s1) (arefs s2))
assume Arefs4: forall (s1:TSet.set abuffer) (s2:TSet.set abuffer).
  TSet.subset s1 s2 ==> TSet.subset (arefs s1) (arefs s2)

(* General disjointness predicate between a buffer and a set of heterogeneous buffers *)
let disjointSet #a (b:buffer a) (bufs:TSet.set abuffer) =
  (forall b'. TSet.mem b' bufs ==> disjoint b b'.b)

(* General disjointness predicate between a buffer and a set of heterogeneous references *)
let disjointRef #a (b:buffer a) (set:TSet.set Heap.aref) = 
  ~(TSet.mem (as_aref b) set)

(* Similar but specialized disjointness predicates *)
let disjoint_1 a b = disjoint a b
let disjoint_2 a b b' = disjoint a b /\ disjoint a b'
let disjoint_3 a b b' b'' = disjoint a b /\ disjoint a b' /\ disjoint a b''
let disjoint_4 a b b' b'' b''' = disjoint a b /\ disjoint a b' /\ disjoint a b'' /\ disjoint a b'''
let disjoint_5 a b b' b'' b''' b'''' = disjoint a b /\ disjoint a b' /\ disjoint a b'' /\ disjoint a b''' /\ disjoint a b''''

let disjoint_ref_1 a r = as_aref a =!= r
let disjoint_ref_2 a r r' = as_aref a =!= r /\ as_aref a =!= r'
let disjoint_ref_3 a r r' r'' = as_aref a =!= r /\ as_aref a =!= r' /\ as_aref a =!= r''
let disjoint_ref_4 a r r' r'' r''' = as_aref a =!= r /\ as_aref a =!= r' /\ as_aref a =!= r'' /\ as_aref a =!= r'''
let disjoint_ref_5 a r r' r'' r''' r'''' = as_aref a =!= r /\ as_aref a =!= r' /\ as_aref a =!= r'' /\ as_aref a =!= r''' /\ as_aref a =!= r''''

(* General modifies clause for buffers only *)
let modifies_buf rid buffs h h' =
  modifies_ref rid (arefs buffs) h h'
  /\ (forall (#a:Type) (b:buffer a). (frameOf b = rid /\ live h b /\ disjointSet b buffs) ==> equal h b h' b)

(* General modifies clause for buffers and references *)
let modifies_buf_ref rid buffs refs h h' =
  modifies_ref rid (TSet.union (arefs buffs) refs) h h'
  /\ (forall (#a:Type) (b:buffer a). (frameOf b = rid /\ live h b /\ disjointSet b buffs /\ disjointRef b refs) ==> equal h b h' b)

(* Specialized versions (to speed up verification) *)
let modifies_buf_0 rid h h' =
  modifies_ref rid !{} h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb = rid /\ live h bb) ==> equal h bb h' bb)

let modifies_buf_1 (#t:Type) rid (b:buffer t) h h' =
  modifies_ref rid !{as_ref b} h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb = rid /\ live h bb /\ disjoint b bb) ==> equal h bb h' bb)

let modifies_buf_2 (#t:Type) (#t':Type) rid (b:buffer t) (b':buffer t') h h' =
  modifies_ref rid !{as_ref b, as_ref b'} h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb = rid /\ live h bb /\ disjoint b bb /\ disjoint b' bb) 
       ==> equal h bb h' bb)

let modifies_buf_3 (#t:Type) (#t':Type) (#t'':Type) rid (b:buffer t) (b':buffer t') (b'':buffer t'') h h' =
  modifies_ref rid !{as_ref b, as_ref b', as_ref b''} h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb = rid /\ live h bb /\ disjoint b bb /\ disjoint b' bb /\ disjoint b'' bb) 
       ==> equal h bb h' bb)

let modifies_buf_4 (#t:Type) (#t':Type) (#t'':Type) (#t''':Type) rid (b:buffer t) (b':buffer t') (b'':buffer t'') (b''':buffer t''') h h' =
  modifies_ref rid !{as_ref b, as_ref b', as_ref b'', as_ref b'''} h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb = rid /\ live h bb /\ disjoint b bb /\ disjoint b' bb /\ disjoint b'' bb /\ disjoint b''' bb) 
       ==> equal h bb h' bb)

(* TODO: write combinations for references and references + buffers *)

(* General lemmas *)
val disjoint_only_lemma: #a:Type -> #a':Type -> b:buffer a -> b':buffer a' -> Lemma
  (requires (disjoint b b'))
  (ensures (disjointSet b (only b')))
let disjoint_only_lemma #t #t' b b' = ()  

let modifies_trans rid bufs h0 h1 h2 :
  Lemma (requires (modifies_buf rid bufs h0 h1 /\ modifies_buf rid bufs h1 h2))
	(ensures (modifies_buf rid bufs h0 h2))
	[SMTPat (modifies_buf rid bufs h0 h1); SMTPat (modifies_buf rid bufs h1 h2)]
 = ()

let modifies_sub rid bufs subbufs h0 h1 :
  Lemma
    (requires (TSet.subset subbufs bufs /\ modifies_buf rid subbufs h0 h1))
    (ensures (modifies_buf rid bufs h0 h1))
    [SMTPatT (modifies_buf rid subbufs h0 h1); SMTPat (TSet.subset subbufs bufs)]
 = ()

let modifies_none h : Lemma (modifies Set.empty h h) = ()

val lemma_aux_0: #a:Type -> #a':Type -> h0:mem -> h1:mem -> bufs:TSet.set abuffer -> b:buffer a -> b':buffer a' -> Lemma
  (requires (~(live h0 b') /\ live h0 b /\ disjointSet b (bufs++b') ))
  (ensures (disjointSet b bufs))
  [SMTPat (modifies_buf h0.tip (bufs++b') h0 h1); SMTPat (live h0 b)]
let lemma_aux_0 #a #a' h0 h1 bufs b b' = ()

val lemma_aux_3: #a:Type -> #a':Type -> h:Heap.heap -> b:Heap.ref a -> b':Heap.ref a' -> Lemma
  (requires (Heap.contains h b /\ ~(Heap.contains h b')))
  (ensures (Heap.Ref b =!= Heap.Ref b'))
let lemma_aux_3 #a #a' h b b' = ()

val lemma_aux_2: #a:Type -> #a':Type -> h:mem -> b:buffer a -> b':buffer a' -> Lemma
  (requires (live h b /\ ~(contains h b')))
  (ensures (disjoint b b'))
  [SMTPat (disjoint b b'); SMTPat (live h b)]
let lemma_aux_2 #a #a' h b b' = lemma_live_1 h (content b) (content b')

val lemma_aux_1: #a:Type -> #a':Type -> h0:mem -> h1:mem -> bufs:TSet.set abuffer -> b:buffer a -> b':buffer a' -> Lemma
  (requires (~(contains h0 b') /\ live h0 b /\ disjointSet b bufs))
  (ensures (disjointSet b (bufs++b')))
  [SMTPat (modifies_buf h0.tip bufs h0 h1); SMTPat (~(live h0 b')); SMTPat (live h0 b)]
let lemma_aux_1 #a #a' h0 h1 bufs b b' = ()

val modifies_fresh: #a:Type -> h0:mem -> h1:mem -> bufs:TSet.set abuffer -> b:buffer a -> Lemma
  (requires (~(contains h0 b) /\ contains h1 b /\ frameOf b = h0.tip
    /\ modifies (Set.singleton h0.tip) h0 h1
    /\ modifies_buf h0.tip (bufs ++ b) h0 h1))
  (ensures (~(contains h0 b) /\ contains h1 b /\ frameOf b = h0.tip
    /\ modifies (Set.singleton h0.tip) h0 h1
    /\ modifies_buf h0.tip bufs h0 h1 ))
let modifies_fresh #a h0 h1 bufs b = ()

(* Specialized lemmas *)
let modifies_trans_0_0 rid h0 h1 h2 :
  Lemma (requires (modifies_buf_0 rid h0 h1 /\ modifies_buf_0 rid h1 h2))
	(ensures (modifies_buf_0 rid h0 h2))
	[SMTPat (modifies_buf_0 rid h0 h1); SMTPat (modifies_buf_0 rid h1 h2)]
 = ()

let modifies_trans_1_0 rid b h0 h1 h2 :
  Lemma (requires (modifies_buf_1 rid b h0 h1 /\ modifies_buf_0 rid h1 h2))
	(ensures (modifies_buf_1 rid b h0 h2))
	[SMTPat (modifies_buf_1 rid b h0 h1); SMTPat (modifies_buf_0 rid h1 h2)]
 = ()

let modifies_trans_0_1 rid b h0 h1 h2 :
  Lemma (requires (modifies_buf_0 rid h0 h1 /\ modifies_buf_1 rid b h1 h2))
	(ensures (modifies_buf_1 rid b h0 h2))
	[SMTPat (modifies_buf_0 rid h0 h1); SMTPat (modifies_buf_1 rid b h1 h2)]
 = ()

let modifies_trans_1_1 rid b h0 h1 h2 :
  Lemma (requires (modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid b h1 h2))
	(ensures (modifies_buf_1 rid b h0 h2))
	[SMTPat (modifies_buf_1 rid b h0 h1); SMTPat (modifies_buf_1 rid b h1 h2)]
 = ()

let modifies_trans_2_0 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_0 rid h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPat (modifies_buf_2 rid b b' h0 h1); SMTPat (modifies_buf_0 rid h1 h2)]
 = ()

let modifies_trans_2_1 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_1 rid b h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPat (modifies_buf_2 rid b b' h0 h1); SMTPat (modifies_buf_1 rid b h1 h2)]
 = ()

let modifies_trans_2_1' rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_2 rid b' b h0 h1 /\ modifies_buf_1 rid b h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPat (modifies_buf_2 rid b' b h0 h1); SMTPat (modifies_buf_1 rid b h1 h2)]
 = ()

let modifies_trans_0_2 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_0 rid h0 h1 /\ modifies_buf_2 rid b b' h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPat (modifies_buf_0 rid h0 h1); SMTPat (modifies_buf_2 rid b b' h1 h2)]
 = ()

let modifies_trans_1_2 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_1 rid b h0 h1 /\ modifies_buf_2 rid b b' h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPat (modifies_buf_1 rid b h0 h1); SMTPat (modifies_buf_2 rid b b' h1 h2)]
 = ()

let modifies_trans_2_2 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_2 rid b b' h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPat (modifies_buf_2 rid b b' h0 h1); SMTPat (modifies_buf_2 rid b b' h1 h2)]
 = ()

let modifies_trans_3_3 rid b b' b'' h0 h1 h2 :
  Lemma (requires (modifies_buf_3 rid b b' b'' h0 h1 /\ modifies_buf_3 rid b b' b'' h1 h2))
	(ensures (modifies_buf_3 rid b b' b'' h0 h2))
	[SMTPat (modifies_buf_3 rid b b' b'' h0 h1); SMTPat (modifies_buf_3 rid b b' b'' h1 h2)]
 = ()

let modifies_trans_4_4 rid b b' b'' b''' h0 h1 h2 :
  Lemma (requires (modifies_buf_4 rid b b' b'' b''' h0 h1 /\ modifies_buf_4 rid b b' b'' b''' h1 h2))
	(ensures (modifies_buf_4 rid b b' b'' b''' h0 h2))
	[SMTPat (modifies_buf_4 rid b b' b'' b''' h0 h1); SMTPat (modifies_buf_4 rid b b' b'' b''' h1 h2)]
 = ()

(* TODO: complete with specialized versions of every general lemma *)

(* Modifies clauses that do not change the shape of the HyperStack (h1.tip = h0.tip) *)
(* abstract *) let modifies_0 h0 h1 = 
  modifies_one h0.tip h0 h1 /\ modifies_buf_0 h0.tip h0 h1

(* abstract *) let modifies_1 (#a:Type) (b:buffer a) h0 h1 =
  let rid = frameOf b in
  modifies_one rid h0 h1 /\ modifies_buf_1 rid b h0 h1

(* abstract *) let modifies_2_1 (#a:Type) (b:buffer a) h0 h1 =
  let rid = frameOf b in
  ((rid = h0.tip /\ modifies_buf_1 rid b h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid <> h0.tip /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h  
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_0 h0.tip h0 h1 ))

(* abstract *) let modifies_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 =
  let rid = frameOf b in let rid' = frameOf b' in
  ((rid = rid' /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid <> rid' /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h1.h  
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 ))

(* abstract *) let modifies_3 (#a:Type) (#a':Type) (#a'':Type) (b:buffer a) (b':buffer a')  (b'':buffer a'') h0 h1 =
  let rid = frameOf b in let rid' = frameOf b' in let rid'' = frameOf b'' in
  ((rid = rid' /\ rid' = rid'' /\ modifies_buf_3 rid b b' b'' h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid = rid' /\ rid' <> rid'' /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_1 rid'' b'' h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid'')) h0.h h1.h )
  \/ (rid <> rid' /\ rid' = rid'' /\ modifies_buf_2 rid' b' b'' h0 h1 /\ modifies_buf_1 rid b h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid'')) h0.h h1.h )
  \/ (rid = rid'' /\ rid' <> rid'' /\ modifies_buf_2 rid b b'' h0 h1 /\ modifies_buf_1 rid' b' h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h1.h )
  \/ (rid <> rid' /\ rid' <> rid'' /\ rid <> rid'' 
      /\ HH.modifies_just (Set.union (Set.union (Set.singleton rid) (Set.singleton rid')) (Set.singleton rid'')) h0.h h1.h  
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_1 rid'' b'' h0 h1))

(* abstract *) let modifies_3_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 =
  let rid = frameOf b in let rid' = frameOf b' in
  ((rid = rid' /\ rid' = h0.tip /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid = rid' /\ rid' <> h0.tip /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_0 h0.tip h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h )
  \/ (rid <> rid' /\ rid = h0.tip /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid') (Set.singleton h0.tip)) h0.h h1.h )
  \/ (rid <> rid' /\ rid' = h0.tip /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_1 rid b h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h )
  \/ (rid <> rid' /\ rid' <> h0.tip /\ rid <> h0.tip
      /\ HH.modifies_just (Set.union (Set.union (Set.singleton rid) (Set.singleton rid')) (Set.singleton h0.tip)) h0.h h1.h  
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_0 h0.tip h0 h1))

(* abstract *) let modifies_region rid bufs h0 h1 =
  modifies_one rid h0 h1 /\ modifies_buf rid bufs h0 h1

let lemma_stl_1 (#a:Type) (b:buffer a) h0 h1 h2 h3 : Lemma
  (requires (live h0 b /\ fresh_frame h0 h1 /\ modifies_1 b h1 h2 /\ popped h2 h3))
  (ensures  (modifies_1 b h0 h3))
  [SMTPat (modifies_1 b h1 h2); SMTPat (fresh_frame h0 h1); SMTPat (popped h2 h3)]
  = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // OK

let lemma_stl_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 h3 : Lemma
  (requires (live h0 b /\ live h0 b' /\ fresh_frame h0 h1 /\ modifies_2 b b' h1 h2 /\ popped h2 h3))
  (ensures  (modifies_2 b b' h0 h3))
  [SMTPat (modifies_2 b b' h1 h2); SMTPat (fresh_frame h0 h1); SMTPat (popped h2 h3)]
  = () 

#reset-options

let lemma_modifies_0_trans h0 h1 h2 : Lemma
  (requires (modifies_0 h0 h1 /\ modifies_0 h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPat (modifies_0 h0 h1); SMTPat (modifies_0 h1 h2)]
  = ()

let lemma_modifies_1_trans (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (modifies_1 b h0 h1 /\ modifies_1 b h1 h2))
  (ensures (modifies_1 b h0 h2))
  [SMTPat (modifies_1 b h0 h1); SMTPat (modifies_1 b h1 h2)]
  = ()

let lemma_modifies_2_1_trans (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (modifies_2_1 b h0 h1 /\ modifies_2_1 b h1 h2))
  (ensures (modifies_2_1 b h0 h2))
  [SMTPat (modifies_2_1 b h0 h1); SMTPat (modifies_2_1 b h1 h2)]
  = ()

let lemma_modifies_2_trans (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ live h1 b /\ live h1 b'
    /\ modifies_2 b b' h0 h1 /\ modifies_2 b b' h1 h2))
  (ensures (modifies_2 b b' h0 h2))
  [SMTPat (modifies_2 b b' h0 h1); SMTPatT (modifies_2 b b' h1 h2)]
  = ()

let lemma_modifies_2_trans' (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ live h1 b /\ live h1 b'
    /\ modifies_2 b b' h0 h1 /\ modifies_2 b b' h1 h2))
  (ensures (modifies_2 b b' h0 h2))
  [SMTPat (modifies_2 b' b h0 h1); SMTPatT (modifies_2 b b' h1 h2)]
  = ()

#reset-options "--z3timeout 20"
#set-options "--lax" // OK

let lemma_modifies_2_refl (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 : Lemma
  (requires (True))
  (ensures  (modifies_2 b b' h0 h1 <==> modifies_2 b' b h0 h1))
  [SMTPat (modifies_2 b b' h0 h1)]
  = ()

#reset-options "--z3timeout 20"
#set-options "--lax" // OK

let lemma_modifies_3_trans (#a:Type) (#a':Type) (#a'':Type) (b:buffer a) (b':buffer a') (b'':buffer a'') h0 h1 h2 : Lemma
  (requires (modifies_3 b b' b'' h0 h1 /\ modifies_3 b b' b'' h1 h2))
  (ensures (modifies_3 b b' b'' h0 h2))
  [SMTPat (modifies_3 b b' b'' h0 h1); SMTPat (modifies_3 b b' b'' h1 h2)]
  = ()

#reset-options

#reset-options "--z3timeout 20"

let lemma_modifies_3_2_trans (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ live h1 b /\ live h1 b'
    /\ modifies_3_2 b b' h0 h1 /\ modifies_3_2 b b' h1 h2))
  (ensures (modifies_3_2 b b' h0 h2))
  [SMTPat (modifies_3_2 b b' h0 h1); SMTPat (modifies_3_2 b b' h1 h2)]
  = ()

val lemma_modifies_0_0: h0:mem -> h1:mem -> h2:mem -> Lemma
  (requires (modifies_0 h0 h1 /\ modifies_0 h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPat (modifies_0 h0 h1); SMTPat (modifies_0 h1 h2)]
let lemma_modifies_0_0 h0 h1 h2 = ()

#reset-options "--z3timeout 20"

let lemma_modifies_1_0 (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h1 b /\ modifies_1 b h0 h1 /\ modifies_0 h1 h2))
  (ensures  (live h2 b /\ modifies_2_1 b h0 h2))
  [SMTPat (modifies_1 b h0 h1); SMTPat (modifies_0 h1 h2)]
  = ()

let lemma_modifies_0_1 (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (live h0 b /\ modifies_0 h0 h1 /\ modifies_1 b h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPat (modifies_0 h0 h1); SMTPat (modifies_1 b h1 h2)]
  = ()

let lemma_modifies_0_1' (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (~(contains h0 b) /\ modifies_0 h0 h1 /\ live h1 b /\ modifies_1 b h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPat (modifies_0 h0 h1); SMTPat (modifies_1 b h1 h2)]
  = ()

#reset-options "--z3timeout 100"

let lemma_modifies_1_1 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ disjoint b b'
    /\ modifies_1 b h0 h1 /\ modifies_1 b' h1 h2))
  (ensures  (modifies_2 b b' h0 h2 /\ modifies_2 b' b h0 h2))
  [SMTPat (modifies_1 b h0 h1); SMTPat (modifies_1 b' h1 h2)]
  = ()

let lemma_modifies_0_2 (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ ~(contains h0 b') /\ modifies_0 h0 h1 /\ live h1 b'
    /\ frameOf b' = h0.tip /\ modifies_2 b b' h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPat (modifies_2 b b' h1 h2); SMTPat (modifies_0 h0 h1)]
  = ()

let lemma_modifies_0_2' (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ ~(contains h0 b') /\ modifies_0 h0 h1 /\ live h1 b'
    /\ frameOf b' = h0.tip /\ modifies_2 b' b h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPat (modifies_2 b' b h1 h2); SMTPat (modifies_0 h0 h1)]
  = ()

let lemma_modifies_1_2 (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ modifies_1 b h0 h1 /\ ~(contains h0 b') /\ live h1 b' /\
    modifies_2 b b' h1 h2 /\ frameOf b' = h0.tip))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPat (modifies_1 b h0 h1); SMTPat (modifies_2 b b' h1 h2)]  
  = ()

let lemma_modifies_1_2' (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ modifies_1 b h0 h1 /\ ~(contains h0 b') /\ live h1 b' /\
    modifies_2 b' b h1 h2 /\ frameOf b' = h0.tip))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPat (modifies_1 b h0 h1); SMTPat (modifies_2 b' b h1 h2)]  
  = ()

let lemma_modifies_1_2'' (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ modifies_1 b h0 h1 /\ modifies_2 b b' h1 h2))
  (ensures  (modifies_2 b b' h0 h2))
  [SMTPat (modifies_1 b h0 h1); SMTPat (modifies_2 b b' h1 h2)]  
  = ()

let lemma_modifies_1_2''' (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ modifies_1 b h0 h1 /\ modifies_2 b' b h1 h2))
  (ensures  (modifies_2 b' b h0 h2))
  [SMTPat (modifies_1 b h0 h1); SMTPat (modifies_2 b' b h1 h2)]  
  = ()

let lemma_modifies_1_1_prime (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ modifies_1 b h0 h1 /\ ~(contains h0 b') /\ live h1 b' /\
    modifies_1 b' h1 h2 /\ frameOf b' = h0.tip))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPat (modifies_1 b h0 h1); SMTPat (modifies_1 b' h1 h2)]  
  = ()

let lemma_modifies_2_1 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ disjoint b b'
    /\ modifies_2 b b' h0 h1 /\ modifies_1 b h1 h2))
  (ensures  (modifies_2 b b' h0 h2))
  [SMTPat (modifies_2 b b' h0 h1); SMTPat (modifies_1 b h1 h2)]
  = ()

let lemma_modifies_2_1' (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ disjoint b b'
    /\ modifies_2 b' b h0 h1 /\ modifies_1 b h1 h2))
  (ensures  (modifies_2 b' b h0 h2))
  [SMTPat (modifies_2 b' b h0 h1); SMTPat (modifies_1 b h1 h2)]
  = ()

(* TODO: lemmas for modifies_3 *)

(* Axiomatization issue with 'arefs' *)
let lemma_modifies_buf_0 (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (~(contains h0 b) /\ live h1 b /\ modifies_buf (frameOf b) !{} h0 h1
    /\ modifies_buf (frameOf b) (only b) h1 h2))
  (ensures (modifies_buf (frameOf b) !{} h0 h2))
  = let rid = frameOf b in
    let h = Map.sel h0.h rid in
    let h' = Map.sel h1.h rid in
    let h'' = Map.sel h2.h rid in
    cut (Heap.modifies !{} h h'); 
    cut (Heap.modifies (arefs (only b)) h' h'');
    assert(TSet.equal !{} empty);
    assert(TSet.equal (arefs (TSet.union empty (TSet.singleton (Buff b))))
		     (TSet.union (arefs empty) (TSet.singleton (as_aref b))) );
    assert(TSet.equal (TSet.union empty (TSet.singleton (Buff b))) (only b));
    TSet.lemma_equal_intro (arefs (only b)) !{as_ref b}
  
#reset-options

val lemma_modifies_fresh_2: #t:Type -> #t':Type -> a:buffer t -> b:buffer t' -> h0:mem -> h1:mem -> Lemma
  (requires (~(contains h0 b) /\ live h1 b /\ frameOf b = h0.tip /\ modifies_2 a b h0 h1))
  (ensures (~(contains h0 b) /\ live h1 b /\ frameOf b = h0.tip
    /\ modifies_buf_1 (frameOf a) a h0 h1 ))
let lemma_modifies_fresh_2 #t #t' a b h0 h1 = ()

(** Concrete getters and setters **)
let create #a (init:a) (len:UInt32.t) : ST (buffer a)
     (requires (fun h -> True))
     (ensures (fun (h0:mem) b h1 -> ~(contains h0 b) 
       /\ live h1 b /\ idx b = 0 /\ length b = v len /\ frameOf b = h0.tip
       /\ modifies_0 h0 h1
       /\ as_seq h1 b == Seq.create (v len) init
       ))
  = let content = salloc (Seq.create (v len) init) in
    let h = HST.get() in
    let b = {content = content; idx = (uint_to_t 0); length = len} in
    Seq.lemma_eq_intro (as_seq h b) (sel h b);
    b


let index #a (b:buffer a) (n:UInt32.t{v n<length b}) : STL a
     (requires (fun h -> live h b))
     (ensures (fun h0 z h1 -> live h0 b /\ h1 == h0
       /\ z == Seq.index (as_seq h0 b) (v n)))
  = let s = !b.content in
    Seq.index s (v b.idx+v n)

// TODO
let lemma_aux_6 #a (b:buffer a) (n:UInt32.t{v n < length b}) (z:a) h0 : Lemma
  (requires (live h0 b))
  (ensures (live h0 b
    /\ modifies_1 b h0 (HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z)) ))
  [SMTPat (HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z))]
  = let h1 = HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z) in
    assume (forall (#a':Type) (b':buffer a'). (live h0 b' /\ disjointSet b' (only b)) ==> equal h0 b' h1 b')

val upd: #a:Type -> b:buffer a -> n:UInt32.t -> z:a -> STL unit
  (requires (fun h -> live h b /\ v n < length b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ v n < length b
    /\ modifies_1 b h0 h1
    /\ as_seq h1 b == Seq.upd (as_seq h0 b) (v n) z ))
    (* /\ get h1 b (v n) == z *)
    (* /\ (forall (i:nat). {:pattern (get h1 b i)} (i < length b /\ i <> v n) ==> get h1 b i == get h0 b i) *)
let upd #a b n z =
  let s0 = !b.content in
  let s = Seq.upd s0 (v b.idx + v n) z in
  b.content := s;
  let h = HST.get() in
  Seq.lemma_eq_intro (as_seq h b) (Seq.slice s (idx b) (idx b + length b));
  Seq.lemma_eq_intro (Seq.upd (Seq.slice s0 (idx b) (idx b + length b)) (v n) z)
  		     (Seq.slice (Seq.upd s0 (idx b + v n) z) (idx b) (idx b + length b));
  ()

(* Could be made Total with a couple changes in the spec *)
let sub #a (b:buffer a) (i:UInt32.t) (len:UInt32.t{v len <= length b /\ v i + v len <= length b}) : STL (buffer a)
     (requires (fun h -> live h b))
     (ensures (fun h0 b' h1 -> content b == content b' /\ idx b' = idx b + v i /\ length b' = v len 
       /\ h0 == h1 /\ includes b b' /\ live h1 b' /\ live h0 b
       /\ as_seq h1 b' == Seq.slice (as_seq h0 b) (v i) (v i + v len) ))
  = let b' = {content = b.content; idx = i +^ b.idx; length = len} in
    let h = HST.get() in
    Seq.lemma_eq_intro (as_seq h b') (Seq.slice (as_seq h b) (v i) (v i + v len));
    b'

let offset #a (b:buffer a) (i:UInt32.t{v i <= length b}) : STL (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> content b' == content b /\ idx b' = idx b + v i /\ length b' = length b - v i
    /\ h0 == h1 /\ includes b b' /\ live h1 b'
    /\ as_seq h1 b' == Seq.slice (as_seq h0 b) (v i) (length b) ))
  = let b' = {content = b.content; idx = i +^ b.idx; length = b.length -^ i} in
    let h = HST.get() in
    Seq.lemma_eq_intro (as_seq h b') (Seq.slice (as_seq h b) (v i) (length b));
    b'

let lemma_modifies_one_trans_1 (#a:Type) (b:buffer a) (h0:mem) (h1:mem) (h2:mem): Lemma
  (requires (modifies_one (frameOf b) h0 h1 /\ modifies_one (frameOf b) h1 h2))
  (ensures (modifies_one (frameOf b) h0 h2))
  [SMTPat (modifies_one (frameOf b) h0 h1); SMTPat (modifies_one (frameOf b) h1 h2)]
  = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // TODO: restore after switching to FStar.Seq-based specification

private val blit_aux: #a:Type -> b:buffer a -> idx_b:UInt32.t -> 
  b':buffer a -> idx_b':UInt32.t -> len:UInt32.t{v idx_b+v len<=length b/\v idx_b'+v len<= length b'} -> 
  ctr:UInt32.t{v ctr <= v len} ->  STL unit
  (requires (fun h -> live h b /\ live h b' /\ disjoint b b'
    /\ (forall (i:nat). i < v ctr ==> get h b (v idx_b+i) == get h b' (v idx_b'+i)) ))
  (ensures (fun h0 _ h1 -> live h1 b /\ live h1 b'  /\ live h0 b /\ live h0 b' 
    /\ disjoint b b' /\ length b >= v idx_b+v len /\ length b' >= v idx_b'+v len
    /\ modifies_1 b' h0 h1
    /\ (forall (i:nat). {:pattern (get h1 b' (v idx_b'+i))} i < v len 
	==> get h0 b (v idx_b+i) == get h1 b' (v idx_b'+i))
    /\ (forall (i:nat). {:pattern (get h1 b' i)} (i < v idx_b' \/ (i >= v idx_b'+v len /\ i < length b')) 
	==> get h1 b' i == get h0 b' i) ))
let rec blit_aux #a b idx_b b' idx_b' len ctr = 
  let h0 = HST.get() in
  if (len -^ ctr) =^ (uint_to_t 0) then ()
  else 
  begin
    let bctr = index b (idx_b +^ ctr) in
    upd b' (idx_b' +^ ctr) bctr;
    blit_aux b idx_b b' idx_b' len (ctr +^ (uint_to_t 1))
  end

#reset-options
#set-options "--lax"

val blit: #t:Type -> a:buffer t -> idx_a:UInt32.t{v idx_a <= length a} -> b:buffer t{disjoint a b} -> 
  idx_b:UInt32.t{v idx_b <= length b} -> len:UInt32.t{v idx_a+v len <= length a /\ v idx_b+v len <= length b} -> STL unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 a /\ live h1 b /\ live h1 a
      (* /\ (forall (i:nat). {:pattern (get h1 b (v idx_b+i))} i < v len ==> get h1 b (v idx_b+i) == get h0 a (v idx_a+i)) *)
      (* /\ (forall (i:nat). {:pattern (get h1 b i)} ((i >= v idx_b + v len /\ i < length b) \/ i < v idx_b) ==> get h1 b i == get h0 b i) *)
      /\ Seq.slice (as_seq h1 b) (v idx_b) (v idx_b+v len) == Seq.slice (as_seq h0 a) (v idx_a) (v idx_a+v len)
      /\ Seq.slice (as_seq h1 b) 0 (v idx_b) == Seq.slice (as_seq h0 b) 0 (v idx_b)
      /\ Seq.slice (as_seq h1 b) (v idx_b+v len) (length b) == Seq.slice (as_seq h0 b) (v idx_b+v len) (length b)
      /\ modifies_1 b h0 h1 ))
let blit #t a idx_a b idx_b len = blit_aux a idx_a b idx_b len (uint_to_t 0)

#reset-options

assume val fill: #t:Type -> b:buffer t -> z:t -> len:UInt32.t{v len <= length b} -> STL unit
  (requires (fun h -> live h b))
  (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    /\ Seq.slice (as_seq h1 b) 0 (v len) == Seq.create (v len) z
    /\ Seq.slice (as_seq h1 b) (v len) (length b) == Seq.slice (as_seq h0 b) (v len) (length b) ))

#reset-options

val split: #a:Type -> a:buffer t -> i:UInt32.t{v i <= length a} -> STL (buffer t * buffer t)
    (requires (fun h -> live h a))
    (ensures (fun h0 b h1 -> live h1 (fst b) /\ live h1 (snd b) /\ h1 == h0 /\ idx (fst b) = idx a 
      /\ idx (snd b) = idx a + v i /\ length (fst b) = v i /\ length (snd b) = length a - v i 
      /\ disjoint (fst b) (snd b)  /\ content (fst b) == content a /\ content (snd b) == content a
      /\ as_seq h1 (fst b) == Seq.slice (as_seq h0 a) 0 (v i)
      /\ as_seq h1 (snd b) == Seq.slice (as_seq h0 a) (v i) (length a) ))
let split #t a i = 
  let a1 = sub a (uint_to_t 0) i in let a2 = sub a i (a.length -^ i) in a1, a2

#set-options "--lax" // TODO: FIX

private val of_seq_aux: #a:Type -> s:bounded_seq a -> l:UInt32.t{v l = Seq.length s} -> ctr:UInt32.t{v ctr <= v l} -> b:buffer a{idx b = 0 /\ length b = v l} -> STL unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b 
      /\ (forall (i:nat). {:pattern (get h1 b i)} i < v ctr ==> get h1 b i == Seq.index s i)
      /\ (forall (i:nat). {:pattern (get h1 b i)} i >= v ctr /\ i < length b ==> get h1 b i == get h0 b i)
      /\ modifies_1 b h0 h1 ))
let rec of_seq_aux #a s l ctr b =
  if ctr =^ (uint_to_t 0) then ()
  else 
  begin
    let j = ctr -^ (uint_to_t 1) in 
    upd b j (Seq.index s (v j));
    of_seq_aux s l j b	 
  end

val of_seq: #a:Type -> s:seq a -> l:UInt32.t{v l = Seq.length s /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> True))
  (ensures (fun h0 b h1 -> idx b = 0 /\ length b = v l /\ ~(contains h0 b) /\ live h1 b
    /\ frameOf b = h1.tip
    /\ modifies_region h1.tip TSet.empty h0 h1
    /\ sel h1 b == (Seq.slice s 0 (v l)) ))
let of_seq #a s l =
  let s' = salloc (Seq.slice s 0 (v l)) in
  {content = s'; idx = 0ul; length = l}

val clone: #a:Type ->  b:buffer a -> l:UInt32.t{length b >= v l /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> ~(contains h0 b') /\ live h0 b /\ live h1 b' /\ idx b' = 0 /\ length b' = v l
    /\ (forall (i:nat). {:pattern (get h1 b' i)} i < v l ==> get h1 b' i == get h0 b i)
    /\ modifies_0 h0 h1
    ))
let clone #a b l =
  let (init:a) = index b (uint_to_t 0) in 
  let (b':buffer a) = create init l in 
  blit b (uint_to_t 0) b' (uint_to_t 0) l; 
  b'

#reset-options

val no_upd_lemma_0: #t:Type -> h0:mem -> h1:mem -> b:buffer t -> Lemma
  (requires (live h0 b /\ modifies_0 h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPat (modifies_0 h0 h1); SMTPat (live h0 b)]
let no_upd_lemma_0 #t h0 h1 b = ()

val no_upd_lemma_1: #t:Type -> #t':Type -> h0:mem -> h1:mem -> a:buffer t -> b:buffer t' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ modifies_1 a h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPat (modifies_1 a h0 h1); SMTPat (live h0 b)]
let no_upd_lemma_1 #t #t' h0 h1 a b = ()

val no_upd_lemma_2: #t:Type -> #t':Type -> #t'':Type -> h0:mem -> h1:mem -> a:buffer t -> a':buffer t' -> b:buffer t'' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ disjoint a' b /\ modifies_2 a a' h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPat (live h0 b); SMTPat (modifies_2 a a' h0 h1)]
let no_upd_lemma_2 #t #t' #t'' h0 h1 a a' b = ()

val no_upd_lemma_2_1: #t:Type -> #t':Type -> h0:mem -> h1:mem -> a:buffer t -> b:buffer t' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ modifies_2_1 a h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPat (live h0 b); SMTPat (modifies_2_1 a h0 h1)]
let no_upd_lemma_2_1 #t #t' h0 h1 a b = ()

val no_upd_fresh: #t:Type -> h0:mem -> h1:mem -> a:buffer t -> Lemma
  (requires (live h0 a /\ fresh_frame h0 h1))
  (ensures  (live h0 a /\ live h1 a /\ equal h0 a h1 a))
  [SMTPat (live h0 a); SMTPat (fresh_frame h0 h1)]
let no_upd_fresh #t h0 h1 a = ()

val no_upd_popped: #t:Type -> h0:mem -> h1:mem -> b:buffer t -> Lemma
  (requires (live h0 b /\ frameOf b <> h0.tip /\ popped h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPat (live h0 b); SMTPat (popped h0 h1)]
let no_upd_popped #t h0 h1 b = ()

let eq_lemma_0 (#t:Type) h0 h1 (b:buffer t) : Lemma
  (requires (modifies_0 h0 h1 /\ live h0 b))
  (ensures  (live h0 b /\ live h1 b /\ (forall (i:nat). {:pattern (get h1 b i)} i < length b ==> get h1 b i == get h0 b i) ))
  = ()

let eq_lemma_1 (#t:Type) (#t':Type) h0 h1 (a:buffer t) (b:buffer t') : Lemma 
  (requires (modifies_1 a h0 h1 /\ disjoint a b /\ live h0 b))
  (ensures  (live h0 b /\ live h1 b /\ (forall (i:nat). {:pattern (get h1 b i)} i < length b 
					       ==> get h1 b i == get h0 b i)))
  = ()

let eq_lemma_2 (#t:Type) (#t':Type) (#t'':Type) h0 h1 (a:buffer t) (a':buffer t') (b:buffer t'') : Lemma
  (requires (modifies_2 a a' h0 h1 /\ disjoint a b /\ disjoint a' b /\ live h0 b))
  (ensures  (live h0 b /\ live h1 b /\ (forall (i:nat). {:pattern (get h1 b i)} i < length b ==> get h1 b i == get h0 b i)))
  = ()

let eq_lemma_2_1 (#t:Type) (#t':Type) h0 h1 (b:buffer t) (b':buffer t) : Lemma
  (requires (modifies_2_1 b h0 h1 /\ live h0 b' /\ disjoint b b'))
  (ensures  (live h0 b' /\ live h1 b' /\ (forall (i:nat). {:pattern (get h1 b i)} i < length b' ==> get h1 b' i == get h0 b' i) ))
  = ()

let eq_lemma_fresh h0 h1 a : Lemma
  (requires (live h0 a /\ fresh_frame h0 h1))
  (ensures  (live h0 a /\ live h1 a /\ (forall (i:nat). {:pattern (get h1 a i)} i < length a 
			    ==> get h1 a i == get h0 a i)))
  = ()

val eq_lemma_popped: #t:Type -> h0:mem -> h1:mem -> b:buffer t -> Lemma
  (requires (live h0 b /\ frameOf b <> h0.tip /\ popped h0 h1))
  (ensures  (live h0 b /\ live h1 b 
    /\ (forall (i:nat). {:pattern (get h1 b i)} i < length b ==> get h1 b i == get h0 b i)))
let eq_lemma_popped #t h0 h1 b = ()

(* Modifies of subset lemmas *)
let lemma_modifies_sub_0 h0 h1 : Lemma
  (requires (h1 == h0))
  (ensures  (modifies_0 h0 h1))
  [SMTPat (modifies_0 h0 h1)]
  = ()

let lemma_modifies_sub_1 #t h0 h1 (b:buffer t) : Lemma
  (requires (h1 == h0))
  (ensures  (modifies_1 b h0 h1))
  [SMTPat (live h0 b); SMTPat (modifies_1 b h0 h1)]
  = ()

let lemma_modifies_sub_2 #t #t' h0 h1 (b:buffer t) (b':buffer t') : Lemma
  (requires (h1 == h0))
  (ensures  (modifies_2 b b' h0 h1))
  [SMTPat (live h0 b); SMTPat (live h0 b'); SMTPat (modifies_2 b b' h0 h1)]
  = ()

let lemma_modifies_sub_2_1 #t h0 h1 (b:buffer t) : Lemma
  (requires (modifies_0 h0 h1 /\ live h0 b))
  (ensures  (modifies_2_1 b h0 h1))
  [SMTPat (live h0 b); SMTPat (modifies_2_1 b h0 h1)]
  = ()

#reset-options "--z3timeout 100"

(* TODO *)
let modifies_subbuffer_1 (#t:Type) h0 h1 (sub:buffer t) (a:buffer t) : Lemma
  (requires (live h0 a /\ modifies_1 sub h0 h1 /\ live h1 sub /\ includes a sub))
  (ensures  (modifies_1 a h0 h1 /\ live h1 a))
  [SMTPat (modifies_1 sub h0 h1); SMTPat (includes a sub)]
  = admit() 

(* TODO *)
let modifies_subbuffer_2 (#t:Type) (#t':Type) h0 h1 (sub:buffer t) (a':buffer t') (a:buffer t) : Lemma
  (requires (live h0 a /\ live h0 a' /\ includes a sub /\ modifies_2 sub a' h0 h1 ))
  (ensures  (modifies_2 a a' h0 h1 /\ modifies_2 a' a h0 h1 /\ live h1 a))
  [SMTPat (modifies_2 sub a' h0 h1); SMTPat (includes a sub)]
  = admit()

let modifies_subbuffer_2' (#t:Type) (#t':Type) h0 h1 (sub:buffer t) (a':buffer t') (a:buffer t) : Lemma
  (requires (live h0 a /\ live h0 a' /\ includes a sub /\ modifies_2 a' sub h0 h1 ))
  (ensures  (modifies_2 a a' h0 h1 /\ live h1 a))
  [SMTPat (modifies_2 a' sub h0 h1); SMTPat (includes a sub)]
  = ()

(* TODO *)
let modifies_subbuffer_2_1 (#t:Type) h0 h1 (sub:buffer t) (a:buffer t) : Lemma
  (requires (live h0 a /\ includes a sub /\ modifies_2_1 sub h0 h1))
  (ensures  (modifies_2_1 a h0 h1 /\ live h1 a))
  [SMTPat (modifies_2_1 sub h0 h1); SMTPat (includes a sub)]
  = admit()

let modifies_subbuffer_2_prime (#t:Type) h0 h1 (sub1:buffer t) (sub2:buffer t) (a:buffer t) : Lemma
  (requires (live h0 a /\ includes a sub1 /\ includes a sub2 /\ modifies_2 sub1 sub2 h0 h1))
  (ensures  (modifies_1 a h0 h1 /\ live h1 a))
  [SMTPat (modifies_2 sub1 sub2 h0 h1); SMTPat (includes a sub1); SMTPat (includes a sub2)]
  = ()

let modifies_popped_2 (#t:Type) #t' (a:buffer t) (b:buffer t') h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ live h0 b /\ fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_2 a b h1 h2))
  (ensures  (modifies_2 a b h0 h3))
  [SMTPat (fresh_frame h0 h1); SMTPat (popped h2 h3); SMTPat (modifies_2 a b h1 h2)]
  = ()

let modifies_popped_1 (#t:Type) (a:buffer t) h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_2_1 a h1 h2))
  (ensures  (modifies_1 a h0 h3))
  [SMTPat (fresh_frame h0 h1); SMTPat (popped h2 h3); SMTPat (modifies_2_1 a h1 h2)]
  = ()

let modifies_popped_1' (#t:Type) (a:buffer t) h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_1 a h1 h2))
  (ensures  (modifies_1 a h0 h3))
  [SMTPat (fresh_frame h0 h1); SMTPat (popped h2 h3); SMTPat (modifies_1 a h1 h2)]
  = ()

let modifies_popped_0 h0 h1 h2 h3 : Lemma
  (requires (fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_0 h1 h2))
  (ensures  (modifies_0 h0 h3))
  [SMTPat (fresh_frame h0 h1); SMTPat (popped h2 h3); SMTPat (modifies_0 h1 h2)]
  = ()

let live_popped (#t:Type) (b:buffer t) h0 h1 : Lemma
  (requires (popped h0 h1 /\ live h0 b /\ frameOf b <> h0.tip))
  (ensures  (live h1 b))
  [SMTPat (popped h0 h1); SMTPat (live h0 b)]
  = ()

let live_fresh (#t:Type) (b:buffer t) h0 h1 : Lemma
  (requires (fresh_frame h0 h1 /\ live h0 b))
  (ensures  (live h1 b))
  [SMTPat (fresh_frame h0 h1); SMTPat (live h0 b)]
  = ()

let modifies_0_to_2_1_lemma (#t:Type) h0 h1 (b:buffer t) : Lemma
  (requires (modifies_0 h0 h1 /\ live h0 b))
  (ensures  (modifies_2_1 b h0 h1))
  [SMTPat (modifies_2_1 b h0 h1); SMTPat (live h0 b) ]
  = ()

let lemma_modifies_none_push_pop h0 h1 h2 : Lemma
  (requires (fresh_frame h0 h1 /\ popped h1 h2))
  (ensures  (h2 == h0))
  = admit()

let lemma_modifies_0_push_pop h0 h1 h2 h3 : Lemma
  (requires (fresh_frame h0 h1 /\ modifies_0 h1 h2 /\ popped h2 h3))
  (ensures  (h3 == h0))
  = admit()

let modifies_1_to_2_1_lemma (#t:Type) h0 h1 (b:buffer t) : Lemma
  (requires (modifies_1 b h0 h1 /\ live h0 b))
  (ensures  (modifies_2_1 b h0 h1))
  [SMTPat (modifies_2_1 b h0 h1); SMTPat (live h0 b) ]
  = ()

(* let modifies_1_to_2_lemma (#t:Type) #t' h0 h1 (b:buffer t) (b':buffer t'): Lemma *)
(*   (requires (modifies_1 b h0 h1 /\ live h0 b)) *)
(*   (ensures  (modifies_2 b b' h0 h1)) *)
(*   [SMTPat (modifies_2 b b' h0 h1); SMTPat (live h0 b) ] *)
(*   = () *)

let modifies_poppable_0 h0 h1 : Lemma
  (requires (modifies_0 h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPat (modifies_0 h0 h1)]
  = ()

let modifies_poppable_1 #t h0 h1 (b:buffer t) : Lemma
  (requires (modifies_1 b h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPat (modifies_1 b h0 h1)]
  = ()

let modifies_poppable_2_1 #t h0 h1 (b:buffer t) : Lemma
  (requires (modifies_2_1 b h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPat (modifies_2_1 b h0 h1)]
  = ()

let modifies_poppable_2 #t #t' h0 h1 (b:buffer t) (b':buffer t') : Lemma
  (requires (modifies_2 b b' h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPat (modifies_2 b' b h0 h1)]
  = ()

let modifies_poppable_3_2 #t #t' h0 h1 (b:buffer t) (b':buffer t') : Lemma
  (requires (modifies_3_2 b b' h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPat (modifies_3_2 b' b h0 h1)]
  = ()

let lemma_fresh_poppable h0 h1 : Lemma
  (requires (fresh_frame h0 h1))
  (ensures  (poppable h1))
  [SMTPat (fresh_frame h0 h1)]
  = ()

let lemma_equal_domains_popped h0 h1 h2 h3 : Lemma
  (requires (equal_domains h0 h1 /\ popped h0 h2 /\ popped h1 h3))
  (ensures  (equal_domains h2 h3))  
  = ()

let lemma_equal_domains h0 h1 h2 h3 h4 : Lemma
  (requires (fresh_frame h0 h1 /\ modifies_0 h1 h2 /\ equal_domains h2 h3 /\ popped h3 h4))
  (ensures  (equal_domains h0 h4))
  [SMTPat (fresh_frame h0 h1); SMTPat (modifies_0 h1 h2); SMTPat (popped h3 h4)]
  = ()
