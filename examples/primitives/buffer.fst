module Buffer

open FStar.Seq
open FStar.Heap
open FStar.Array
open FStar.Ghost

(*
  TODO: distinction entre 'ST' et 'STF', le second poussant une 'frame'
  Le premier étant un rafinement disant que la frame n'a pas changé.
  *)

(* Buffer general type, fully implemented on FStar's arrays *)
abstract type buffer (a:Type) = {
  content:array a; 
  idx:nat;    
  length:nat;
}

// JK: should those heap functions not be ghost ? Or returned an erased type ?
let contains #a h (b:buffer a) : GTot bool = Heap.contains #(seq a) h b.content
let sel #a h (b:buffer a) : GTot (seq a) = Heap.sel #(seq a) h b.content
let max_length #a h (b:buffer a) : GTot nat = Seq.length (sel h b)
let length #a (b:buffer a) : GTot nat = b.length
let idx #a (b:buffer a) : GTot nat = b.idx
let content #a (b:buffer a) : GTot (ref (seq a)) = b.content

(* Liveness condition, necessary for any computation on the buffer *)
// JK: coercion is not well enforced between booleans and Type0s
let live #a (h:heap) (b:buffer a) : GTot Type0 = 
  contains h b /\ max_length h b >= length b + idx b

let disjoint #a #a' (b:buffer a) (b':buffer a') : GTot Type0 =
  (b.content =!= b'.content
  \/ (b.content == b'.content  /\ a=a'
     /\ (idx b + length b <= idx b' \/ idx b' + length b' <= idx b)))

(* Defines that sb is a subbuffer of b *)
let subBuffer #a (sb:buffer a) (b:buffer a) : GTot Type0 =
  Heap.Ref b.content == Heap.Ref sb.content /\ idx sb >= idx b
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
assume val arefs: FStar.Set.set abuffer -> Tot (FStar.Set.set aref)

(** TODO: make it minimal & review **)
assume Arefs1: forall (#a:Type) (b:buffer a) (s:FStar.Set.set abuffer). {:pattern (FStar.Set.mem (Ref (content b)) (arefs s))}
	      FStar.Set.mem (Buff b) s ==> FStar.Set.mem (Ref (content b)) (arefs s)
assume Arefs2: forall (s:FStar.Set.set abuffer) (s':FStar.Set.set abuffer). {:pattern (FStar.Set.subset s s')}
	      FStar.Set.subset s s' ==> FStar.Set.subset (arefs s) (arefs s')
assume Arefs3: arefs (reveal empty) = FStar.Set.empty #aref
assume Arefs4: forall (s1:FStar.Set.set abuffer) (s2:FStar.Set.set abuffer). {:pattern (FStar.Set.union s1 s2)}
  FStar.Set.equal (arefs (FStar.Set.union s1 s2)) (FStar.Set.union (arefs s1) (arefs s2))
assume Arefs5: forall (#a:Type) (b:buffer a). {:pattern (arefs (FStar.Set.singleton (Buff b)))}
  FStar.Set.equal (arefs (FStar.Set.singleton (Buff b))) (FStar.Set.singleton (Ref (content b)))

(* Specifies that a buffer is disjoint from a set of abstract buffers *)
let disjointSet (#a:Type) (b:buffer a) (buffs:FStar.Set.set abuffer) : GTot Type0 =
  (forall (#a':Type) (b':buffer a'). {:pattern (FStar.Set.mem (Buff b') buffs) \/ (disjoint b b')} FStar.Set.mem (Buff b') buffs ==> disjoint b b')

let disjointRef #a (b:buffer a) set : GTot Type0 = ~(Set.mem (Ref b.content) set)

let modifies buffs refs h h' = 
  modifies (Set.union (arefs buffs) refs) h h'
  /\ (forall (#a:Type) (b:buffer a). {:pattern (disjointSet b buffs)}
      (live h b /\ disjointSet b buffs /\ disjointRef b refs) ==> equal h b h' b)

(** Lemmas; TODO: give better names, check triggers **)
val disjoint_only_lemma: #a:Type -> #a':Type -> b:buffer a -> b':buffer a' -> Lemma
  (requires (disjoint b b'))
  (ensures (disjointSet b (only b')))
let disjoint_only_lemma #t #t' b b' = ()  

let equal_lemma #a h0 h1 b bufs : 
  Lemma (requires (live h0 b /\ disjointSet b bufs /\ modifies bufs Set.empty h0 h1))
	(ensures (equal h0 b h1 b))
	[SMTPatT (disjointSet b bufs); SMTPatT (modifies bufs Set.empty h0 h1)]
 = ()

let equal_lemma_2 #a h0 h1 b bufs refs : 
  Lemma (requires (live h0 b /\ disjointSet b bufs /\ disjointRef b refs /\ modifies bufs refs h0 h1))
	(ensures (equal h0 b h1 b))
	[SMTPatT (equal h0 b h1 b)]
//	[SMTPatT (disjointSet a bufs); SMTPatT (disjointSet SMTPatT (modifies bufs refs h0 h1)]
 = ()

let modifies_trans bufs h0 h1 h2 :
  Lemma (requires (modifies bufs Set.empty h0 h1 /\ modifies bufs Set.empty h1 h2))
	(ensures (modifies bufs Set.empty h0 h2))
	[SMTPatT (modifies bufs Set.empty h0 h1); SMTPatT (modifies bufs Set.empty h1 h2)]
 = ()

let modifies_trans_2 bufs refs h0 h1 h2 :
  Lemma (requires (modifies bufs refs h0 h1 /\ modifies bufs refs h1 h2))
	(ensures (modifies bufs refs h0 h2))
	[SMTPatT (modifies bufs refs h0 h1); SMTPatT (modifies bufs refs h1 h2)]
 = ()

let modifies_sub bufs subbufs h0 h1 :
  Lemma 
    (requires (Set.subset subbufs bufs /\ modifies subbufs Set.empty h0 h1))
    (ensures (modifies bufs Set.empty h0 h1))
    [SMTPatT (modifies subbufs Set.empty h0 h1); SMTPat (Set.subset subbufs bufs)]
 = ()

let modifies_sub_2 bufs subbufs refs subrefs h0 h1 :
  Lemma 
    (requires (Set.subset subbufs bufs /\ Set.subset subrefs refs /\ modifies subbufs refs h0 h1))
    (ensures (modifies bufs refs h0 h1))
    [SMTPatT (modifies subbufs refs h0 h1); SMTPat (Set.subset subbufs bufs); SMTPatT (Set.subset subrefs refs)]
 = ()

let modifies_none h : Lemma (requires (True)) (ensures (modifies Set.empty Set.empty h h)) = ()

let modifies_fresh #a h0 h1 bufs refs (b:buffer a) :
  Lemma 
    (requires (not(contains h0 b) /\ modifies (bufs ++ b) refs h0 h1))
    (ensures (modifies bufs refs h0 h1))
    [SMTPat (not(contains h0 b)); SMTPatT (modifies (bufs ++ b) refs h0 h1)]
 = ()

(* Equality between fragments of buffers *)
let equalSub (#a:Type) (hb:heap) (b:buffer a) (b_idx:nat) (hb':heap) (b':buffer a) (b_idx':nat) (len:nat) : GTot Type0 =
  (live hb b) /\ (live hb' b') /\ (length b >= b_idx + len) /\ (length b' >= b_idx' + len)
  /\ (forall (i:nat). {:pattern (get hb b) \/ (get hb' b')} i < len ==> get hb b (b_idx+i) == get hb' b' (b_idx'+i))

(* Specifies an atomic update to a buffer *)
let atomicUpdate (#a:Type) h0 h1 (b:buffer a) (n:nat) z : GTot Type0 =
  live h0 b /\ live h1 b /\ n < length b /\ get h1 b n == z /\ max_length h1 b = max_length h0 b 
  /\ (forall (i:nat). {:pattern (get h1 b i)} (i < length b /\ i <> n) ==> get h1 b i == get h0 b i)
  /\ modifies (only b) Set.empty h0 h1
  
(** Concrete getters and setters **)

let create #a (init:a) (len:nat) : 
  ST (buffer a)
     (requires (fun h -> True))
     (ensures (fun h0 b h1 ->
       not(contains h0 b) /\ live h1 b /\ idx b = 0 /\ length b = len 
       /\ modifies Set.empty Set.empty h0 h1
       /\ (forall (i:nat). {:pattern (get h1 b i)} i < len ==> 
	   get h1 b i == init))) 
  = let content = Array.create len init in 
    {content = content; idx = 0; length = len}

let index #a (b:buffer a) (n:nat{n<length b}) : 
  ST a
     (requires (fun h -> live h b))
     (ensures (fun h0 z h1 -> live h0 b /\ (h1 == h0) /\ (z == get h0 b n)))
  = Array.index b.content (b.idx+n)

let upd #a (b:buffer a) (n:nat{n < length b}) v :
  ST unit
     (requires (fun h -> live h b))
     (ensures (fun h0 _ h1 -> atomicUpdate h0 h1 b n v))
  = Array.upd b.content (b.idx+n) v;
    gcut (fun _ -> (Set.mem (Buff b) (only b)))

let sub #a (b:buffer a) (i:nat) (len:nat{len <= length b /\ i + len <= length b}) :
  ST (buffer a)
     (requires (fun h -> live h b))
     (ensures (fun h0 b' h1 -> content b = content b' /\ idx b' = idx b + i /\ length b' = len /\ (h0 == h1)))
  = {content = b.content; idx = i+b.idx; length = len}

#reset-options //"--z3timeout 20"

private let rec blit_aux #a (b:buffer a) (idx_b:nat{idx_b<=length b}) (b':buffer a{disjoint b b'}) (idx_b':nat{idx_b'<=length b'}) (len:nat{idx_b+len <= length b /\ idx_b'+len <= length b'}) (ctr:nat{ctr<=len}) :
  ST unit
    (requires (fun h -> equalSub h b (idx_b+ctr) h b' (idx_b'+ctr) (len-ctr)))
    (ensures (fun h0 _ h1 -> 
      equalSub h1 b idx_b h1 b' idx_b' len /\ modifies (only b') Set.empty h0 h1
      /\ equalSub h0 b' 0 h1 b' 0 idx_b'
      /\ equalSub h0 b' (idx_b'+len) h1 b' (idx_b'+len) (length b' - idx_b' - len)))
  = let h0 = ST.get() in
    match ctr with
    | 0 -> admit()
    | _  -> let i = ctr-1 in
      let bi = index b (idx_b+i) in
      upd b' (idx_b'+i) bi; 
      let h1 = ST.get() in 
      equal_lemma h0 h1 b (only b');
      gcut (fun _ -> get h1 b (idx_b+i) == get h1 b' (idx_b'+i)); 
//      cut (forall (i:nat). i < len - ctr ==> get h1 b' (idx_b'+i) == get h0 b' (idx_b'+i));
//      admit()
      admitP (forall (i:nat). {:pattern (get h1 b (idx_b+ctr+i)) \/ (get h1 b' (idx_b'+ctr+i))} 
	i < len - ctr ==> get h1 b (idx_b+ctr+i) == get h1 b' (idx_b'+ctr+i));
      cut (forall (j:nat). j < len - i ==> get h1 b (idx_b+i+j) == get h1 b' (idx_b'+i+j));
      admit()
      blit_aux b idx_b b' idx_b' len i
    

private val blit_aux: #a:Type -> a:buffer t -> idx_a:nat{idx_a <= length a} -> b:buffer t{disjoint a b} -> 
  idx_b:nat{idx_b <= length b} -> len:nat{idx_a+len <= length a /\ idx_b+len <= length b} ->
  ctr:nat{ctr<=len} -> ST unit
    (requires (fun h -> copyOf h a idx_a b idx_b ctr len))
    (ensures (fun h0 _ h1 -> copyOf h0 a idx_a b idx_b ctr len 
      /\ copyOf h1 a idx_a b idx_b 0 len /\ modifies (only b) h0 h1
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

val blit: #a:Type -> a:buffer t -> idx_a:nat{idx_a <= length a} -> b:buffer t{disjoint a b} -> 
  idx_b:nat{idx_b <= length b} -> len:nat{idx_a+len <= length a /\ idx_b+len <= length b} -> ST unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 b 
      /\ copyOf h1 a idx_a b idx_b 0 len
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} ((i >= idx_b + len /\ i < length b) \/ i < idx_b) ==> v (get h1 b i) = v (get h0 b i))
      /\ modifies (only b) h0 h1))
let blit #t a idx_a b idx_b len = blit_aux a idx_a b idx_b len len

val split: #a:Type -> a:buffer t -> i:nat{i <= length a} -> ST (buffer t * buffer t)
    (requires (fun h -> live h a))
    (ensures (fun h0 b h1 -> live h1 (fst b) /\ live h1 (snd b) /\ h1 == h0 /\ idx (fst b) = idx a 
      /\ idx (snd b) = idx a + i /\ length (fst b) = i /\ length (snd b) = length a - i 
      /\ disjoint (fst b) (snd b)  /\ content (fst b) = content a /\ content (snd b) = content a))
let split #t a i = 
  let a1 = sub a 0 i in let a2 = sub a i (a.length - i) in a1, a2  

val offset: #a:Type -> a:buffer t -> i:nat{i <= length a} -> ST (buffer t)
  (requires (fun h -> live h a))
  (ensures (fun h0 a' h1 -> h0 == h1 /\ content a' = content a /\ idx a' = idx a + i /\ length a' = length a - i))
let offset #t a i = {content = a.content; idx = i+a.idx; length = a.length - i}

private val of_seq_aux: #a:pos -> s:seq (usint a) -> l:pos{l = Seq.length s} -> ctr:nat{ ctr <= l} -> b:buffer a{idx b = 0 /\ length b = l} -> ST unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b 
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < ctr ==> v (get h1 b i) = v (Seq.index s i))
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} i >= ctr /\ i < length b ==> v (get h1 b i) = v (get h0 b i))))
let rec of_seq_aux #a s l ctr b =
  let h0 = ST.get() in
  match ctr with
  | 0 -> ()
  | _ -> let j = ctr - 1 in 
         upd b j (Seq.index s j); 
	 of_seq_aux s l j b	 

val of_seq: #a:pos -> s:seq (usint a) -> l:pos{l = Seq.length s} -> ST (buffer a)
  (requires (fun h -> True))
  (ensures (fun h0 b h1 -> idx b = 0 /\ length b = l /\ not(contains h0 b) /\ live h1 b
    /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < l ==> v (get h1 b i) = v (Seq.index s i)) ))
let of_seq #a s l =
  let init = Seq.index s 0 in
  let b = create #a init l in 
  of_seq_aux s l l b; 
  b


// TODO: Change to clone
val copy: #a:pos ->  b:buffer a -> l:pos{length b >= l} -> ST (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> not(contains h0 b') /\ contains h1 b' /\ idx b' = 0 
	      /\ length b' = l /\ copyOf #a h1 b 0 b' 0 0 l
	      /\ modifies empty h0 h1))
let copy #a b l =
  let init = index b 0 in 
  let b' = create init l in 
  blit b 0 b' 0 l; 
  b'
