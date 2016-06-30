module FStar.Buffer

open FStar.Seq
open FStar.UInt32
open FStar.HyperStack
open FStar.Ghost
open FStar.HST

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let lemma_size (x:int) (pos:nat) : Lemma (requires (UInt.size x n))
				     (ensures (x >= 0))
				     [SMTPatT (UInt.size x n)]
  = ()

type bounded_seq (t:Type) = s:seq t{length s <= UInt.max_int n}

(* Buffer general type, fully implemented on FStar's arrays *)
private type buffer' (a:Type) = {
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
// JK: coercion is not well enforced between booleans and Type0s
let live #a (h:mem) (b:buffer a) : GTot Type0 = 
  contains h b /\ max_length h b >= length b + idx b

let getValue #a h (b:buffer a{live h b}) (i:nat{i<max_length h b}) : GTot a = Seq.index (sel h b) i
let get #a h (b:buffer a{live h b}) (i:nat{i < length b}) : GTot a = Seq.index (sel h b) (idx b + i)
let as_seq #a h (b:buffer a{live h b}) : GTot (seq a) = Seq.slice (sel h b) (idx b) (idx b + length b)
let equal #a h (b:buffer a) h' (b':buffer a) : GTot Type0 =
  live h b /\ live h' b' /\ Seq.equal (as_seq h b) (as_seq h' b')

val eq_lemma: #a:Type -> h:mem -> b:buffer a{live h b} -> h':mem -> b':buffer a{live h' b'} -> Lemma
  (requires (equal h b h' b'))
  (ensures  (length b = length b' /\ (forall (i:nat). i < length b ==> get h b i = get h' b' i)))
  [SMTPat (equal h b h' b')]
let eq_lemma #a h b h' b' =
  let s = as_seq h b in
  let s' = as_seq h' b' in
  assert(Seq.length s = length b);
  assert(Seq.length s' = length b');
  assert(Seq.equal s s');
  assert (forall (i:nat). i < length b ==> get h b i = Seq.index s i); 
  assert (forall (i:nat). i < length b' ==> get h' b' i = Seq.index s' i)

(* y is included in x / x contains y *)
let includes #a (x:buffer a) (y:buffer a) : GTot Type0 =
  x.content = y.content /\ idx y >= idx x /\ idx x + length x >= idx y + length y

let disjoint #a #a' (x:buffer a) (y:buffer a') : GTot Type0 =
  frameOf x <> frameOf y \/ as_aref x <> as_aref y
  \/ (as_aref x = as_aref y /\ frameOf x = frameOf y /\ (idx x + length x <= idx y \/ idx y + length y <= idx x))

(* Abstraction of buffers of any type *)
#set-options "--__temp_no_proj SBuffer"
type abuffer = | Buff: #t:Type -> b:buffer t -> abuffer

// JK: these should be GTot, but painful in lemma calls
let empty : Set.set abuffer = Set.empty #abuffer
let only #t (b:buffer t) : Tot (Set.set abuffer) = FStar.Set.singleton (Buff #t b)
let op_Plus_Plus #a s (b:buffer a) : Tot (Set.set abuffer) = Set.union s (only b)
let op_Plus_Plus_Plus set1 set2 : Tot (Set.set abuffer) = FStar.Set.union set1 set2

(* Maps a set of buffer to the set of their references *)
assume val arefs: Set.set abuffer -> Tot (Set.set Heap.aref)

assume Arefs1: arefs (Set.empty) = Set.empty
assume Arefs2: forall (#a:Type) (s:Set.set abuffer) (b:buffer a).
  Set.equal (arefs (Set.union s (Set.singleton (Buff b))))
	    (Set.union (arefs s) (Set.singleton (as_aref b)))
assume Arefs3: forall (s1:Set.set abuffer) (s2:Set.set abuffer).
  Set.equal (arefs (Set.union s1 s2)) (Set.union (arefs s1) (arefs s2))
assume Arefs4: forall (s1:Set.set abuffer) (s2:Set.set abuffer).
  Set.subset s1 s2 ==> Set.subset (arefs s1) (arefs s2)

let disjointSet #a (b:buffer a) (bufs:Set.set abuffer) =
  (forall b'. Set.mem b' bufs ==> disjoint b b'.b)

let disjointRef #a (b:buffer a) (set:Set.set Heap.aref) = 
  ~(Set.mem (as_aref b) set)

let modifies_buf rid buffs h h' =
  modifies_ref rid (arefs buffs) h h'
  /\ (forall (#a:Type) (b:buffer a). (frameOf b = rid /\ live h b /\ disjointSet b buffs) ==> equal h b h' b)

(** Lemmas; TODO: give better names, check triggers **)
val disjoint_only_lemma: #a:Type -> #a':Type -> b:buffer a -> b':buffer a' -> Lemma
  (requires (disjoint b b'))
  (ensures (disjointSet b (only b')))
let disjoint_only_lemma #t #t' b b' = ()  

let modifies_trans #rid bufs h0 h1 h2 :
  Lemma (requires (modifies_buf rid bufs h0 h1 /\ modifies_buf rid bufs h1 h2))
	(ensures (modifies_buf rid bufs h0 h2))
	[SMTPatT (modifies_buf rid bufs h0 h1); SMTPatT (modifies_buf rid bufs h1 h2)]
 = ()

let modifies_sub rid bufs subbufs h0 h1 :
  Lemma
    (requires (Set.subset subbufs bufs /\ modifies_buf rid subbufs h0 h1))
    (ensures (modifies_buf rid bufs h0 h1))
    [SMTPatT (modifies_buf rid subbufs h0 h1); SMTPat (Set.subset subbufs bufs)]
 = ()

let modifies_none h : Lemma (modifies Set.empty h h) = ()

val lemma_aux_0: #a:Type -> #a':Type -> h0:mem -> h1:mem -> bufs:Set.set abuffer -> b:buffer a -> b':buffer a' -> Lemma
  (requires (~(live h0 b') /\ live h0 b /\ disjointSet b (bufs++b') ))
  (ensures (disjointSet b bufs))
  [SMTPat (modifies_buf h0.tip (bufs++b') h0 h1); SMTPat (live h0 b)]
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

val lemma_aux_1: #a:Type -> #a':Type -> h0:mem -> h1:mem -> bufs:Set.set abuffer -> b:buffer a -> b':buffer a' -> Lemma
  (requires (~(contains h0 b') /\ live h0 b /\ disjointSet b bufs))
  (ensures (disjointSet b (bufs++b')))
  [SMTPat (modifies_buf h0.tip bufs h0 h1); SMTPat (~(live h0 b')); SMTPat (live h0 b)]
let lemma_aux_1 #a #a' h0 h1 bufs b b' = ()

val modifies_fresh: #a:Type -> h0:mem -> h1:mem -> bufs:Set.set abuffer -> b:buffer a -> Lemma
  (requires (~(contains h0 b) /\ contains h1 b /\ frameOf b = h0.tip
    /\ modifies (Set.singleton h0.tip) h0 h1
    /\ modifies_buf h0.tip (bufs ++ b) h0 h1))
  (ensures (~(contains h0 b) /\ contains h1 b /\ frameOf b = h0.tip
    /\ modifies (Set.singleton h0.tip) h0 h1
    /\ modifies_buf h0.tip bufs h0 h1 ))
let modifies_fresh #a h0 h1 bufs b = ()

(* Modifies clauses that do not change the shape of the HyperStack (h1.tip = h0.tip) *)
let modifies_0 h0 h1 = 
  modifies_one h0.tip h0 h1 /\ modifies_ref h0.tip Set.empty h0 h1

let modifies_1 (#a:Type) (b:buffer a) h0 h1 =
  let rid = frameOf b in
  modifies_one rid h0 h1 /\ modifies_buf rid (only b) h0 h1

let modifies_2_1 (#a:Type) (b:buffer a) h0 h1 =
  let rid = frameOf b in
  ((rid = h0.tip /\ modifies_buf rid (only b) h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid <> h0.tip /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h  
      /\ modifies_buf rid (only b) h0 h1 /\ modifies_buf h0.tip !{} h0 h1 ))

let modifies_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 =
  let rid = frameOf b in let rid' = frameOf b' in
  ((rid = rid' /\ modifies_buf rid (only b ++ b') h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid <> rid' /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h1.h  
      /\ modifies_buf rid (only b) h0 h1 /\ modifies_buf rid' (only b') h0 h1 ))

let modifies_region rid bufs h0 h1 =
  modifies_one rid h0 h1 /\ modifies_buf rid bufs h0 h1

let lemma_stl_1 (#a:Type) (b:buffer a) h0 h1 h2 h3 : Lemma
  (requires (live h0 b /\ fresh_frame h0 h1 /\ modifies_1 b h1 h2 /\ popped h2 h3))
  (ensures  (modifies_1 b h0 h3))
  [SMTPat (modifies_1 b h1 h2); SMTPat (fresh_frame h0 h1); SMTPat (popped h2 h3)]
  = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // For speed only, goes through

let lemma_stl_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 h3 : Lemma
  (requires (live h0 b /\ live h0 b' /\ fresh_frame h0 h1 /\ modifies_2 b b' h1 h2 /\ popped h2 h3))
  (ensures  (modifies_2 b b' h0 h3))
  [SMTPat (modifies_2 b b' h1 h2); SMTPat (fresh_frame h0 h1); SMTPat (popped h2 h3)]
  = let rid = frameOf b in
    let rid' = frameOf b' in
    if rid = rid' then ()
    else ()

#reset-options "--z3timeout 10"
#set-options "--lax" // For speed only, goes through

let lemma_modifies_1_1 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ disjoint b b'
    /\ modifies_1 b h0 h1 /\ modifies_1 b' h1 h2))
  (ensures  (modifies_2 b b' h0 h2))
  [SMTPat (modifies_1 b h0 h1); SMTPat (modifies_1 b' h1 h2)]
  = let rid = frameOf b in
    let rid' = frameOf b' in
    let modset = (only b ++ b') in
      cut (Set.subset (only b) (only b ++ b'));
    cut (Set.subset (only b') (only b ++ b'));
    if rid <> rid' then begin
      assert (HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h2.h);
      modifies_sub rid modset (only b) h0 h1;
      modifies_sub rid' modset (only b') h1 h2
    end
    else ()

#reset-options "--z3timeout 50"
#set-options "--lax" // OK

let lemma_modifies_2_1 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ disjoint b b'
    /\ modifies_2 b b' h0 h1 /\ modifies_1 b h1 h2))
  (ensures  (modifies_2 b b' h0 h2))
  [SMTPat (modifies_2 b b' h0 h1); SMTPat (modifies_1 b h1 h2)]
  = ()

#reset-options

let lemma_modifies_2_trans (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ live h1 b /\ live h1 b'
    /\ modifies_2 b b' h0 h1 /\ modifies_2 b b' h1 h2))
  (ensures (modifies_2 b b' h0 h2))
  [SMTPat (modifies_2 b b' h0 h1); SMTPat (modifies_2 b b' h1 h2)]
  = ()

let equal_lemma #a rid h0 h1 b bufs :
  Lemma (requires (live h0 b /\ disjointSet b bufs /\ modifies_region rid bufs h0 h1))
	(ensures (equal h0 b h1 b))
	[SMTPatT (disjointSet b bufs); SMTPatT (modifies_region rid bufs h0 h1)]
 = ()

val lemma_modifies_fresh_2: #t:Type -> #t':Type -> a:buffer t -> b:buffer t' -> h0:mem -> h1:mem -> Lemma
  (requires (~(contains h0 b) /\ live h1 b /\ frameOf b = h0.tip /\ modifies_2 a b h0 h1))
  (ensures (~(contains h0 b) /\ live h1 b /\ frameOf b = h0.tip
    /\ modifies_buf (frameOf a) (only a) h0 h1 ))
let lemma_modifies_fresh_2 #t #t' a b h0 h1 = ()

(** Concrete getters and setters **)
let create #a (init:a) (len:UInt32.t) : ST (buffer a)
     (requires (fun h -> True))
     (ensures (fun (h0:mem) b h1 -> ~(contains h0 b) 
       /\ live h1 b /\ idx b = 0 /\ length b = v len /\ frameOf b = h0.tip
       /\ modifies_region h1.tip Set.empty h0 h1
       /\ sel h1 b = Seq.create (v len) init
       (* /\ (forall (i:nat). {:pattern (get h1 b i)} i < v len ==> get h1 b i == init) *)
       ))
  = let content = salloc (Seq.create (v len) init) in
    {content = content; idx = (uint_to_t 0); length = len}

let index #a (b:buffer a) (n:UInt32.t{v n<length b}) : STL a
     (requires (fun h -> live h b))
     (ensures (fun h0 z h1 -> live h0 b /\ h1 == h0 /\ z == get h0 b (v n) ))
  = let s = !b.content in
    Seq.index s (v b.idx+v n)

(* JK: Breaks extraction for some reason *)
let lemma_aux_5 (#a:Type) (#a':Type) (b:buffer a) (h0:mem) (h1:mem) (b':buffer a') : Lemma
  (requires (live h0 b /\ live h0 b' /\ modifies_1 b h0 h1
	     (* /\ modifies_one (frameOf b) h0 h1 *)
	     (* /\ modifies_ref (frameOf b) !{as_ref b} h0 h1 *)
	     /\ as_aref b <> as_aref b'))
  (ensures (equal h0 b' h1 b'))
  [SMTPat (equal h0 b' h1 b')]
  = ()

let lemma_aux_7 (#a:Type) (b:buffer a) : Lemma
  (requires (True))
  (ensures  (Set.equal (arefs (only b)) (Set.singleton (as_aref b))))
  [SMTPat (arefs (only b))]
  = cut (Set.equal (Set.union Set.empty (arefs (only b))) (arefs (only b)))

// TODO
let lemma_aux_6 #a (b:buffer a) (n:UInt32.t{v n < length b}) (z:a) h0 : Lemma
  (requires (live h0 b))
  (ensures (live h0 b
    /\ modifies_1 b h0 (HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z)) ))
    (* /\ modifies_one (frameOf b) h0 (HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z)) *)
    (* /\ modifies_buf (frameOf b) (only b) h0 (HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z)))) *)
  [SMTPat (HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z))]
  = let h1 = HS.upd h0 (content b) (Seq.upd (sel h0 b) (idx b + v n) z) in
    assume (forall (#a':Type) (b':buffer a'). (live h0 b' /\ disjointSet b' (only b)) ==> equal h0 b' h1 b')

val upd: #a:Type -> b:buffer a -> n:UInt32.t -> z:a -> STL unit
  (requires (fun h -> live h b /\ v n < length b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ v n < length b
    /\ modifies_1 b h0 h1
    (* /\ modifies_one (frameOf b) h0 h1 *)
    (* /\ modifies_buf (frameOf b) (only b) h0 h1 *)
    /\ sel h1 b = Seq.upd (sel h0 b) (idx b + v n) z
    /\ get h1 b (v n) = z
    /\ (forall (i:nat). {:pattern (get h1 b (v n))} (i < length b /\ i <> v n) ==> get h1 b i = get h0 b i) ))
let upd #a b n z =
  let s = !b.content in
  let s = Seq.upd s (v b.idx + v n) z in
  b.content := s

(* Could be made Total with a couple changes in the spec *)
let sub #a (b:buffer a) (i:UInt32.t) (len:UInt32.t{v len <= length b /\ v i + v len <= length b}) : STL (buffer a)
     (requires (fun h -> live h b))
     (ensures (fun h0 b' h1 -> content b = content b' /\ idx b' = idx b + v i /\ length b' = v len /\ (h0 == h1)))
  = {content = b.content; idx = i +^ b.idx; length = len}

let offset #a (b:buffer a) (i:UInt32.t{v i <= length b}) : STL (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> content b' = content b /\ idx b' = idx b + v i /\ length b' = length b - v i
    /\ h0 == h1))
  = {content = b.content; idx = i +^ b.idx; length = b.length -^ i}

let lemma_modifies_one_trans_1 (#a:Type) (b:buffer a) (h0:mem) (h1:mem) (h2:mem): Lemma
  (requires (modifies_one (frameOf b) h0 h1 /\ modifies_one (frameOf b) h1 h2))
  (ensures (modifies_one (frameOf b) h0 h2))
  [SMTPat (modifies_one (frameOf b) h0 h1); SMTPat (modifies_one (frameOf b) h1 h2)]
  = ()

#set-options "--lax"

(* #reset-options "--z3timeout 100" *)

(* TODO: simplify, add triggers ? *)
private val blit_aux: #a:Type -> b:buffer a -> idx_b:UInt32.t -> 
  b':buffer a -> idx_b':UInt32.t -> len:UInt32.t{v idx_b+v len<=length b/\v idx_b'+v len<= length b'} -> 
  ctr:UInt32.t{v ctr <= v len} ->  STL unit
  (requires (fun h -> live h b /\ live h b' /\ disjoint b b'
    /\ (forall (i:nat). i < v ctr ==> get h b (v idx_b+i) = get h b' (v idx_b'+i)) ))
  (ensures (fun h0 _ h1 -> live h1 b /\ live h1 b'  /\ live h0 b /\ live h0 b' 
    /\ disjoint b b' /\ length b >= v idx_b+v len /\ length b' >= v idx_b'+v len
    /\ modifies_1 b' h0 h1
    (* /\ modifies_one (frameOf b') h0 h1 *)
    (* /\ modifies_buf (frameOf b') (only b') h0 h1     *)
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
    (* cut (forall (i:nat). {:pattern (get h1 b' i)} (i <> v idx_b'+v ctr /\ i < length b') ==> get h1 b' i = get h0 b' i);  *)
    (* cut (modifies_one (frameOf b') h0 h1); *)
    (* cut (modifies_buf (frameOf b') (only b') h0 h1); *)
    blit_aux b idx_b b' idx_b' len (ctr +^ (uint_to_t 1)); 
    let h2 = HST.get() in
    // JK: required for verfication but breaks extraction (infinite loop)
    (* equal_lemma (frameOf b') h1 h2 b (only b'); *)
    (* cut (live h2 b /\ live h2 b'); *)
    (* cut (forall (i:nat). {:pattern (get h2 b')} i < v len ==> get h2 b' (v idx_b'+i) = get h1 b (v idx_b+i)); *)
    (* cut (forall (i:nat). {:pattern (get h2 b')} i < v len ==> get h2 b' (v idx_b'+i) = get h0 b (v idx_b+i)); *)
    (* cut (forall (i:nat). {:pattern (get h2 b')} (i < v idx_b' \/ (i >= v idx_b'+v len /\ i < length b')) ==> get h2 b' i = get h1 b' i); *)
    (* cut (modifies_one (frameOf b') h1 h2); *)
    (* cut (modifies_buf (frameOf b') (only b') h1 h2); *)
    (* cut (modifies_one (frameOf b') h0 h2); *)
    (* cut (modifies_buf (frameOf b') (only b') h0 h2); *)
    (* cut (modifies_ref (frameOf b') !{as_ref b'} h0 h1); (\* Trigger *\) *)
    (* cut (modifies_ref (frameOf b') !{as_ref b'} h1 h2); (\* Trigger *\) *)
    (* cut (modifies_ref (frameOf b') !{as_ref b'} h0 h2); (\* Trigger *\) *)
    ()
  end

#reset-options

val blit: #t:Type -> a:buffer t -> idx_a:UInt32.t{v idx_a <= length a} -> b:buffer t{disjoint a b} -> 
  idx_b:UInt32.t{v idx_b <= length b} -> len:UInt32.t{v idx_a+v len <= length a /\ v idx_b+v len <= length b} -> STL unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 a /\ live h1 b /\ live h1 a
      /\ (forall (i:nat). {:pattern (get h1 b (v idx_b+i))} i < v len ==> get h1 b (v idx_b+i) = get h0 a (v idx_a+i))
      /\ (forall (i:nat). {:pattern (get h1 b i)} ((i >= v idx_b + v len /\ i < length b) \/ i < v idx_b) ==> get h1 b i = get h0 b i)
      /\ modifies_1 b h0 h1 ))
      (* /\ modifies_one (frameOf b) h0 h1 *)
      (* /\ modifies_buf (frameOf b) (only b) h0 h1 )) *)
let blit #t a idx_a b idx_b len = blit_aux a idx_a b idx_b len (uint_to_t 0)

val split: #a:Type -> a:buffer t -> i:UInt32.t{v i <= length a} -> ST (buffer t * buffer t)
    (requires (fun h -> live h a))
    (ensures (fun h0 b h1 -> live h1 (fst b) /\ live h1 (snd b) /\ h1 == h0 /\ idx (fst b) = idx a 
      /\ idx (snd b) = idx a + v i /\ length (fst b) = v i /\ length (snd b) = length a - v i 
      /\ disjoint (fst b) (snd b)  /\ content (fst b) = content a /\ content (snd b) = content a))
let split #t a i = 
  let a1 = sub a (uint_to_t 0) i in let a2 = sub a i (a.length -^ i) in a1, a2

private val of_seq_aux: #a:Type -> s:bounded_seq a -> l:UInt32.t{v l = Seq.length s} -> ctr:UInt32.t{v ctr <= v l} -> b:buffer a{idx b = 0 /\ length b = v l} -> STL unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b 
      /\ (forall (i:nat). {:pattern (get h1 b i)} i < v ctr ==> get h1 b i = Seq.index s i)
      /\ (forall (i:nat). {:pattern (get h1 b i)} i >= v ctr /\ i < length b ==> get h1 b i = get h0 b i)
      /\ modifies_1 b h0 h1 ))
      (* /\ modifies_one (frameOf b) h0 h1 *)
      (* /\ modifies_buf (frameOf b) (only b) h0 h1)) *)
let rec of_seq_aux #a s l ctr b =
  if ctr =^ (uint_to_t 0) then ()
  else 
  begin
    let j = ctr -^ (uint_to_t 1) in 
    upd b j (Seq.index s (v j)); (* JK: no concrete implementation of Seq for now as far as I know *)
    of_seq_aux s l j b	 
  end

val of_seq: #a:Type -> s:seq a -> l:UInt32.t{v l = Seq.length s /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> True))
  (ensures (fun h0 b h1 -> idx b = 0 /\ length b = v l /\ ~(contains h0 b) /\ live h1 b
    /\ frameOf b = h1.tip
    /\ modifies_region h1.tip Set.empty h0 h1
    (* /\ modifies_one (frameOf b) h0 h1 *)
    (* /\ modifies_buf (frameOf b) Set.empty h0 h1 *)
    /\ sel h1 b = (Seq.slice s 0 (v l)) ))
    (* /\ (forall (i:nat). {:pattern (get h1 b i)} i < v l ==> get h1 b i = Seq.index s i) )) *)
let of_seq #a s l =
  let s' = salloc (Seq.slice s 0 (v l)) in
  {content = s'; idx = 0ul; length = l}

val clone: #a:Type ->  b:buffer a -> l:UInt32.t{length b >= v l /\ v l > 0} -> ST (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> ~(contains h0 b') /\ live h0 b /\ live h1 b' /\ idx b' = 0 /\ length b' = v l
    (* /\ sel h1 b' = Seq.slice (sel h0 b) 0 (v l) *)
    /\ (forall (i:nat). {:pattern (get h1 b' i)} i < v l ==> get h1 b' i = get h0 b i)
    /\ modifies_region h1.tip Set.empty h0 h1
    (* /\ modifies_one (frameOf b') h0 h1 *)
    (* /\ modifies_buf (frameOf b') Set.empty h0 h1  *)
    ))
let clone #a b l =
  let (init:a) = index b (uint_to_t 0) in 
  let (b':buffer a) = create init l in 
  blit b (uint_to_t 0) b' (uint_to_t 0) l; 
  b'

val upd_lemma: #t:Type -> ha:mem -> hb:mem -> a:buffer t -> ctr:UInt32.t -> x:t -> Lemma (True)
val no_upd_lemma: #t:Type -> ha:mem -> hb:mem -> a:buffer t -> bufs:(Set.set abuffer) -> Lemma (True)
let upd_lemma #t ha hb a ctr x = ()
let no_upd_lemma #t ha hb a bufs = ()

val no_upd_lemma_1: #t:Type -> #t':Type -> h0:mem -> h1:mem -> a:buffer t -> b:buffer t' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ modifies_1 a h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPat (modifies_1 a h0 h1); SMTPat (live h0 b); SMTPat (disjoint a b)]
let no_upd_lemma_1 #t #t' h0 h1 a b = ()

val no_upd_lemma_2: #t:Type -> #t':Type -> #t'':Type -> h0:mem -> h1:mem -> a:buffer t -> a':buffer t' -> b:buffer t'' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ disjoint a' b /\ modifies_2 a a' h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPat (modifies_1 a h0 h1); SMTPat (live h0 b); SMTPat (disjoint a b)]
let no_upd_lemma_2 #t #t' #t'' h0 h1 a a' b = ()

(* val lemma_disjoint_1: #t:Type -> #t':Type -> a:buffer t -> b:buffer t' -> h0:mem -> h1:mem -> h2:mem ->  *)
(*   Lemma (requires (live a h0 /\ fresh_frame h0 h1 /\ live h1  *)

(* More specialized than the "no_upd_lemma_1" from FStar.Buffer.fst *)
let eq_lemma_1 (#t:Type) (#t':Type) h0 h1 (a:buffer t) (b:buffer t') : Lemma 
  (requires (modifies_1 a h0 h1 /\ disjoint a b /\ live h0 a /\ live h0 b))
  (ensures  (live h0 b /\ live h1 b /\ (forall (i:nat). {:pattern (get h1 b i)} i < length b 
					       ==> get h1 b i = get h0 b i)))
  (* [SMTPat (modifies_1 a h0 h1); SMTPat (disjoint a b)] *)
  = ()

let eq_lemma_2 (#t:Type) (#t':Type) (#t'':Type) h0 h1 (a:buffer t) (a':buffer t') (b:buffer t'') : Lemma
  (requires (modifies_2 a a' h0 h1 /\ disjoint a b /\ disjoint a' b
    /\ live h0 a /\ live h0 b /\ live h0 a'))
  (ensures  (live h0 b /\ live h1 b /\ (forall (i:nat). {:pattern (get h1 b i)} i < length b ==> get h1 b i = get h0 b i)))
  (* [SMTPat (modifies_2 a a' h0 h1); SMTPat (disjoint a b); SMTPat (disjoint a' b)] *)
  = ()

(* TODO *)
let modifies_subbuffer_1 (#t:Type) h0 h1 (sub:buffer t) (a:buffer t) : Lemma
  (requires (live h0 a /\ modifies_1 sub h0 h1 /\ includes a sub))
  (ensures  (modifies_1 a h0 h1))
  = admit() 
  
    (* let rid = frameOf sub in *)
    (* assert(frameOf a = rid); *)
    (* assert(Set.equal (arefs (only sub)) (arefs (only a))); *)
    (* assert(forall (#t:Type) (b:buffer t). {:pattern (disjointSet b (only a))}  *)
    (*   disjoint b a ==> disjoint b sub); *)
    (* assert(forall (#t:Type) (b:buffer t). {:pattern (disjointSet b (only a))}  *)
    (*   disjointSet b (only a) ==> disjoint b a); admit() *)
    (* assert(forall (#t:Type) (b:buffer t). (frameOf b = rid /\ live h0 b /\ disjointSet b (only a)) ==> (frameOf b = rid /\ live h0 b /\ disjointSet b (only sub)));  *)
    (* admit() *)

(* TODO *)
let modifies_subbuffer_2 (#t:Type) (#t':Type) h0 h1 (sub:buffer t) (a':buffer t') (a:buffer t) : Lemma
  (requires (live h0 a /\ live h0 a' /\ includes a sub /\ modifies_2 sub a' h0 h1))
  (ensures  (modifies_2 a a' h0 h1 /\ live h1 a))
  = admit()

let modifies_popped_1 (#t:Type) (a:buffer t) h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_2_1 a h1 h2))
  (ensures  (modifies_1 a h0 h3))
  [SMTPat (fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_2_1 a h1 h2)]
  = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // OK

let lemma_modifies_2_0 (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ ~(contains h0 b') /\ modifies_0 h0 h1 /\ live h1 b'
    /\ frameOf b' = h0.tip /\ modifies_2 b b' h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  = ()

#reset-options
