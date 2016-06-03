module SBuffer

open SInt
open FStar.Seq
open FStar.Heap
open FStar.Array
open FStar.Ghost

(* Buffer general type *)
private type buffer (t:pos) = {
  content:array (usint t); // length "max_length"
  idx:nat; 
  length:nat; // idx + length <= max_length
}

// Required library types because the parameter value is erased 
// at extraction
type uint32s = buffer 32
type uint8s = buffer 8
type uint63s = buffer 63
type uint64s = buffer 64
type uint128s = buffer 128

(* Ghost spec-related functions *)
val contains: heap -> #size:pos -> buffer size -> GTot bool
let contains h #size (b:buffer size) = FStar.Heap.contains #(seq (usint size)) h b.content

val sel: heap -> #size:pos -> buffer size -> GTot (seq (usint size))
let sel h #size b = FStar.Heap.sel h b.content

val max_length: heap -> #size:pos -> buffer size -> GTot nat
let max_length h #size b = FStar.Seq.length (sel h b)

val length: #size:pos -> buffer size -> GTot nat
let length #size b = b.length

val elength: #size:pos -> buffer size -> Tot (erased nat)
let elength #size b = hide b.length

val idx: #size:pos -> buffer size -> GTot nat
let idx #size b = b.idx

val content: #size:pos -> buffer size -> GTot (ref (seq (usint size)))
let content #size b = b.content

(* Liveness condition, necessary for any computation on the buffer *)
let live (h:heap) (#size:pos) (b:buffer size) : GTot Type0 = (contains h b /\ max_length h b >= length b + idx b)

(* Memory separation condition, obtained either when getting a fresh buffer or
   when getting disjoint subbuffers *)
let disjoint (#t:pos) (#t':pos) (b:buffer t) (b':buffer t') : GTot Type0 =
  (b.content =!= b'.content
  \/ (b.content == b'.content
     /\ t=t'
     /\ (idx b + length b <= idx b' \/ idx b' + length b' <= idx b)))

(* Defines that sb is a subbuffer of b *)
let subBuffer (#t:pos) (sb:buffer t) (b:buffer t) : GTot Type0 =
  (FStar.Heap.Ref b.content == FStar.Heap.Ref sb.content)
  /\ idx sb >= idx b /\ idx b + length b >= idx sb + length sb

(* Ghost getters for specs *)
val getValue: h:heap -> #size:pos -> b:buffer size -> i:nat{i<max_length h b} -> GTot (usint size)
let getValue h #size b i = Seq.index (sel h b) i

val get: h:heap -> #size:pos -> b:buffer size{live h b} -> i:nat{i<length b} -> GTot (usint size)
let get h #size b i = Seq.index (sel h b) (idx b + i)

(* Equality between buffers of sints *)
let equal (#a:pos) (h0:heap) (b:buffer a) (h1:heap) (c:buffer a) : GTot Type0 =
  live h0 b /\ live h1 c /\ length b = length c /\ 
  (forall (i:nat). {:pattern (get h0 b i) \/ (get h1 c i)} i < length b ==> v (get h0 b i) = v (get h1 c i))

(* Abstraction of buffers of any type *)
#set-options "--__temp_no_proj SBuffer"
type abuffer = | Buff: #t:pos -> b:buffer t -> abuffer

let empty = FStar.Set.empty #abuffer
let only #t b = FStar.Set.singleton (Buff #t b)
val op_Plus_Plus: s:FStar.Set.set abuffer -> #t:pos -> b:buffer t -> Tot (s':FStar.Set.set abuffer{FStar.Set.subset s s' /\ FStar.Set.subset (only b) s'})
let op_Plus_Plus set #t b = FStar.Set.union set (only b)

let op_Plus_Plus_Plus set1 set2 = FStar.Set.union set1 set2


(* Maps a set of buffer to the set of their references *)
assume val arefs: FStar.Set.set abuffer -> Tot (FStar.Set.set aref)

(** TODO: make it minimal & review **)
assume Arefs1: forall (#size:pos) (b:buffer size) (s:FStar.Set.set abuffer). {:pattern (FStar.Set.mem (Ref (content b)) (arefs s))}
	      FStar.Set.mem (Buff b) s ==> FStar.Set.mem (Ref (content b)) (arefs s)
assume Arefs2: forall (s:FStar.Set.set abuffer) (s':FStar.Set.set abuffer). {:pattern (FStar.Set.subset s s')}
	      FStar.Set.subset s s' ==> FStar.Set.subset (arefs s) (arefs s')
assume Arefs3: arefs empty = FStar.Set.empty #aref
assume Arefs4: forall (s1:FStar.Set.set abuffer) (s2:FStar.Set.set abuffer). {:pattern (FStar.Set.union s1 s2)}
  FStar.Set.equal (arefs (FStar.Set.union s1 s2)) (FStar.Set.union (arefs s1) (arefs s2))
assume Arefs5: forall (#t:pos) (b:buffer t). {:pattern (arefs (FStar.Set.singleton (Buff b)))}
  FStar.Set.equal (arefs (FStar.Set.singleton (Buff b))) (FStar.Set.singleton (Ref (content b)))

(* Specifies that a buffer is disjoint from a set of abstract buffers *)
let disjointSet (#t:pos) (b:buffer t) (buffs:FStar.Set.set abuffer) : GTot Type0 =
  (forall (#t':pos) (b':buffer t'). {:pattern (FStar.Set.mem (Buff b') buffs) \/ (disjoint b b')} FStar.Set.mem (Buff b') buffs ==> disjoint b b')

(* Buffer specific modifies clause *)
// TODO: too restrictive when changing also references to other types
let modifies_buf (buffs:FStar.Set.set abuffer) (h:heap) (h':heap) : GTot Type0 =
  modifies (arefs buffs) h h'
//  FStar.Heap.equal h' (FStar.Heap.concat h' (FStar.Heap.restrict h (FStar.Set.complement (arefs buffs))))
  /\ (forall (#t:pos) (b:buffer t). {:pattern (disjointSet b buffs)}
				  (live h b /\ disjointSet b buffs) ==> equal h b h' b)

(** Lemmas; TODO: give better names, check triggers **)
val disjoint_only_lemma: #t:pos -> b:buffer t -> #t':pos -> b':buffer t' -> Lemma
  (requires (disjoint b b'))
  (ensures (disjointSet b (only b')))
let disjoint_only_lemma #t b #t' b' = ()  

val eq_lemma: h0:heap -> h1:heap -> #size:pos -> a:buffer size -> mods:FStar.Set.set abuffer ->
  Lemma (requires (live h0 a /\ disjointSet a mods /\ modifies_buf mods h0 h1))
	(ensures (equal h0 a h1 a))
	[SMTPatT (disjointSet a mods); SMTPatT (modifies_buf mods h0 h1)]
let eq_lemma h0 h1 #size a mods = ()

val modifies_transitivity_lemma: mods: FStar.Set.set abuffer -> h0:heap -> h1:heap -> h2:heap -> 
  Lemma (requires (modifies_buf mods h0 h1 /\ modifies_buf mods h1 h2))
	(ensures (modifies_buf mods h0 h2))
	[SMTPatT (modifies_buf mods h0 h1); SMTPatT (modifies_buf mods h1 h2)]
let modifies_transitivity_lemma mods h0 h1 h2 = ()

val modifies_subset_lemma: mods:FStar.Set.set abuffer -> submods:FStar.Set.set abuffer ->  h0:heap -> 
  h1:heap -> Lemma 
    (requires (FStar.Set.subset submods mods /\ modifies_buf submods h0 h1))
    (ensures (modifies_buf mods h0 h1))
    [SMTPatT (modifies_buf submods h0 h1); SMTPat (FStar.Set.subset submods mods)]
let modifies_subset_lemma mods submods h0 h1 =
  cut (modifies (arefs mods) h0 h1);
  cut (forall (#t:pos) (b:buffer t). (live h0 b /\ disjointSet b mods) ==> (live h0 b /\ disjointSet b submods) ==> equal h0 b h1 b)

val modifies_empty_lemma: h:heap -> Lemma (requires (True)) (ensures (modifies_buf empty h h))
let modifies_empty_lemma h = ()

val modifies_fresh_lemma: h0:heap -> h1:heap -> mods:FStar.Set.set abuffer -> #size:pos -> 
  b:buffer size -> Lemma 
    (requires (not(contains h0 b) /\ modifies (arefs (mods ++ b)) h0 h1))
    (ensures (modifies (arefs mods) h0 h1))
let modifies_fresh_lemma h0 h1 mods #size b = ()

val modifies_fresh: h0:heap -> h1:heap -> mods:FStar.Set.set abuffer -> #size:pos -> b:buffer size ->
  Lemma (requires (not(contains h0 b) /\ modifies_buf (mods ++ b) h0 h1))
	(ensures (modifies_buf (mods) h0 h1))
	[SMTPat (not(contains h0 b)); SMTPatT (modifies_buf (mods ++ b) h0 h1)]
let modifies_fresh h0 h1 mods #size b =
  cut (FStar.Set.mem (Buff b) (mods ++ b) /\ True); 
  cut (forall (#t:pos) (s:buffer t). (disjointSet s mods /\ disjoint s b) ==> disjointSet s (mods ++ b))

val modifies_subbuffer_lemma: h0:heap -> h1:heap -> mods:FStar.Set.set abuffer -> #size:pos ->
  b:buffer size -> b':buffer size -> Lemma 
    (requires (modifies_buf (mods ++ b) h0 h1 /\ subBuffer #size b b'))
    (ensures (modifies_buf (mods ++ b') h0 h1))
    [SMTPatT (modifies_buf (mods ++ b) h0 h1); SMTPatT (subBuffer #size b b')]
let modifies_subbuffer_lemma h0 h1 mods #size b b' =
  cut (FStar.Set.mem (Buff b') (mods ++ b') /\ True); 
  cut (forall (#t:pos) (s:buffer t). (disjointSet s mods /\ disjoint s b) ==> disjointSet s (mods ++ b))

(* Equality between fragments of buffers *)
let equalSub (#t:pos) (ha:heap) (a:buffer t) (a_idx:nat) (hb:heap) (b:buffer t) (b_idx:nat) (len:nat) : GTot Type0 =
  (live ha a) /\ (live hb b) /\ (length a >= a_idx + len) /\ (length b >= b_idx + len)
  /\ (forall (i:nat). {:pattern (get ha a (a_idx+i)) \/ (get hb b (b_idx+i))} i < len ==> v (get ha a (a_idx+i)) = v (get hb b (b_idx+i)))

(* Specifies an atomic update to a buffer *)
let atomicUpdate (#a:pos) (h0:heap) (h1:heap) (b:buffer a) (n:nat) (z:usint a) : GTot Type0 =
  live h0 b /\ live h1 b /\ n < length b /\ v (get h1 b n) = v z /\ max_length h1 b = max_length h0 b 
  /\ (forall (i:nat). {:pattern (get h1 b i)} (i < length b /\ i <> n) ==> v (get h1 b i) = v (get h0 b i))
  /\ modifies_buf (only b) h0 h1
  
(** TODO: merge with equalSub ? **)
let copyOf (#t:pos) (h:heap) (a:buffer t) (idx_a:nat) (b:buffer t) (idx_b:nat) (ctr:nat) (len:nat) : GTot Type0 =
  idx_a <= length a /\ idx_b <= length b /\ idx_a+len <= length a /\ idx_b+len <= length b /\ ctr <= len /\
  live h a /\ live h b /\ 
  (forall (i:nat). {:pattern (get h a (idx_a+i)) \/ (get h b (idx_b+i))} (i >= ctr /\ i < len) ==>
    v (get h a (idx_a+i)) = v (get h b (idx_b+i)))

(** Concrete getters and setters **)

// TODO: how to allocate without initializing while still preventing
// reads to the buffer (which may contain secrets) before a write ?
// TODO: see what happens if len is just 'nat'
val create: #a:pos -> init:usint a -> len:pos -> ST (buffer a)
  (requires (fun h -> True))
  (ensures (fun h0 b h1 ->
    not(contains h0 b) /\ live h1 b /\ idx b = 0 /\ length b = len 
    /\ modifies_buf empty h0 h1
    /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < len ==> 
	v (get h1 b i) = v init)))
let create #a init len =
  let content = FStar.Array.create len init in 
  {content = content; idx = 0; length = len}

val index: #a:pos -> b:buffer a -> n:nat{n < length b} -> ST (usint a)
  (requires (fun h -> live h b))
  (ensures (fun h0 z h1 -> live h0 b /\ (h1 == h0) /\ (v z == v (get h0 b n))))
let index #a b n = Array.index b.content (b.idx+n)

val upd: #a:pos -> b:buffer a -> n:nat{n < length b} -> v:usint a -> ST unit
  (requires (fun h -> live h b))
  (ensures (fun h0 _ h1 -> atomicUpdate h0 h1 b n v))
let upd #a b n z =
  FStar.Array.upd b.content (b.idx+n) z;
  cut (b2t (FStar.Set.mem (Buff b) (only b)))
  
val sub: #a:pos -> b:buffer a -> i:nat -> len:nat{len <= length b /\ i + len <= length b} -> 
  ST (buffer a)
    (requires (fun h -> live h b))
    (ensures (fun h0 b' h1 -> content b = content b' /\ idx b' = idx b + i /\ length b' = len /\ (h0 == h1)))
let sub #a b i len =
  {content = b.content; idx = i+b.idx; length = len}

private val blit_aux: #t:pos -> a:buffer t -> idx_a:nat{idx_a <= length a} -> b:buffer t{disjoint a b} -> 
  idx_b:nat{idx_b <= length b} -> len:nat{idx_a+len <= length a /\ idx_b+len <= length b} ->
  ctr:nat{ctr<=len} -> ST unit
    (requires (fun h -> copyOf h a idx_a b idx_b ctr len))
    (ensures (fun h0 _ h1 -> copyOf h0 a idx_a b idx_b ctr len 
      /\ copyOf h1 a idx_a b idx_b 0 len /\ modifies_buf (only b) h0 h1
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} ((i >= idx_b + ctr /\ i < length b) \/ i < idx_b) ==> v (get h1 b i) = v (get h0 b i))))
let rec blit_aux #t a idx_a b idx_b len ctr =
  let h0 = ST.get() in
  match ctr with
  | 0 -> ()
  | _  -> let i = ctr-1 in
    let ai = index a (idx_a+i) in
    upd b (idx_b+i) ai; 
    let h1 = ST.get() in 
    eq_lemma h0 h1 a (only b); 
    blit_aux a idx_a b idx_b len i

val blit: #t:pos -> a:buffer t -> idx_a:nat{idx_a <= length a} -> b:buffer t{disjoint a b} -> 
  idx_b:nat{idx_b <= length b} -> len:nat{idx_a+len <= length a /\ idx_b+len <= length b} -> ST unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 b 
      /\ copyOf h1 a idx_a b idx_b 0 len
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} ((i >= idx_b + len /\ i < length b) \/ i < idx_b) ==> v (get h1 b i) = v (get h0 b i))
      /\ modifies_buf (only b) h0 h1))
let blit #t a idx_a b idx_b len = blit_aux a idx_a b idx_b len len

val split: #t:pos -> a:buffer t -> i:nat{i <= length a} -> ST (buffer t * buffer t)
    (requires (fun h -> live h a))
    (ensures (fun h0 b h1 -> live h1 (fst b) /\ live h1 (snd b) /\ h1 == h0 /\ idx (fst b) = idx a 
      /\ idx (snd b) = idx a + i /\ length (fst b) = i /\ length (snd b) = length a - i 
      /\ disjoint (fst b) (snd b)  /\ content (fst b) = content a /\ content (snd b) = content a))
let split #t a i = 
  let a1 = sub a 0 i in let a2 = sub a i (a.length - i) in a1, a2  

val offset: #t:pos -> a:buffer t -> i:nat{i <= length a} -> ST (buffer t)
  (requires (fun h -> live h a))
  (ensures (fun h0 a' h1 -> h0 == h1 /\ content a' = content a /\ idx a' = idx a + i /\ length a' = length a - i))
let offset #t a i = {content = a.content; idx = i+a.idx; length = a.length - i}

private val of_seq_aux: #a:pos -> s:seq (usint a) -> l:pos{l = FStar.Seq.length s} -> ctr:nat{ ctr <= l} -> b:buffer a{idx b = 0 /\ length b = l} -> ST unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b 
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < ctr ==> v (get h1 b i) = v (FStar.Seq.index s i))
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} i >= ctr /\ i < length b ==> v (get h1 b i) = v (get h0 b i))))
let rec of_seq_aux #size s l ctr b =
  let h0 = ST.get() in
  match ctr with
  | 0 -> ()
  | _ -> let j = ctr - 1 in 
         upd b j (FStar.Seq.index s j); 
	 of_seq_aux s l j b	 

val of_seq: #a:pos -> s:seq (usint a) -> l:pos{l = FStar.Seq.length s} -> ST (buffer a)
  (requires (fun h -> True))
  (ensures (fun h0 b h1 -> idx b = 0 /\ length b = l /\ not(contains h0 b) /\ live h1 b
    /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < l ==> v (get h1 b i) = v (FStar.Seq.index s i)) ))
let of_seq #size s l =
  let init = FStar.Seq.index s 0 in
  let b = create #size init l in 
  of_seq_aux s l l b; 
  b

val copy: #a:pos ->  b:buffer a -> l:pos{length b >= l} -> ST (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> not(contains h0 b') /\ contains h1 b' /\ idx b' = 0 
	      /\ length b' = l /\ copyOf #a h1 b 0 b' 0 0 l
	      /\ modifies_buf empty h0 h1))
let copy #size b l =
  let init = index b 0 in 
  let b' = create init l in 
  blit b 0 b' 0 l; 
  b'
