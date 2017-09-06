module FStar.Buffer
 
open FStar.HyperStack.ST
open FStar.Seq
open FStar.UInt32
open FStar.HyperStack
open FStar.Ghost


module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--initial_fuel 0 --max_fuel 0"

//17-01-04 usage? move to UInt? 
let lemma_size (x:int) : Lemma (requires (UInt.size x n))
				     (ensures (x >= 0))
				     [SMTPat (UInt.size x n)]
  = ()

(* Buffer general type, fully implemented on FStar's arrays *)
noeq private type _buffer (a:Type) =
  | MkBuffer: max_length:UInt32.t
    -> content:reference (s:seq a{Seq.length s == v max_length})
    -> idx:UInt32.t
    -> length:UInt32.t{v idx + v length <= v max_length}
    -> _buffer a

(* Exposed buffer type *)
type buffer (a:Type) = _buffer a

(* Ghost getters for specifications *)
// TODO: remove `contains` after replacing all uses with `live`
let contains #a h (b:buffer a) : GTot Type0 = HS.contains h b.content
let unused_in #a (b:buffer a) h : GTot Type0 = HS.unused_in b.content h

(* In most cases `as_seq` should be used instead of this one. *)
let sel #a h (b:buffer a) : GTot (seq a) = HS.sel h b.content

let max_length #a (b:buffer a) : GTot nat = v b.max_length
let length #a (b:buffer a) : GTot nat = v b.length
let idx #a (b:buffer a) : GTot nat = v b.idx

//17-01-04 rename to container or ref? 
let content #a (b:buffer a) :
  GTot (reference (s:seq a{Seq.length s == v b.max_length})) = b.content

(* Lifting from buffer to reference *)
let as_ref #a (b:buffer a) = as_ref (content b)
let as_addr #a (b:buffer a) = as_addr (content b)
let frameOf #a (b:buffer a) : GTot HH.rid = frameOf (content b)

(* Liveliness condition, necessary for any computation on the buffer *)
let live #a (h:mem) (b:buffer a) : GTot Type0 = HS.contains h b.content
let unmapped_in #a (b:buffer a) (h:mem) : GTot Type0 = unused_in b h

val recall: #a:Type
  -> b:buffer a{is_eternal_region (frameOf b) && not (is_mm b.content)} -> Stack unit
  (requires (fun m -> True))
  (ensures  (fun m0 _ m1 -> m0 == m1 /\ live m1 b))
let recall #a b = recall b.content
 
(* Ghostly access an element of the array, or the full underlying sequence *)
let as_seq #a h (b:buffer a) : GTot (s:seq a{Seq.length s == length b}) =
  Seq.slice (sel h b) (idx b) (idx b + length b)

let get #a h (b:buffer a) (i:nat{i < length b}) : GTot a =
  Seq.index (as_seq h b) i

(* Equality predicate on buffer contents, without quantifiers *)
//17-01-04 revise comment? rename?
let equal #a h (b:buffer a) h' (b':buffer a) : GTot Type0 =
  as_seq h b == as_seq h' b'

(* y is included in x / x contains y *)
let includes #a (x:buffer a) (y:buffer a) : GTot Type0 =
  x.max_length == y.max_length /\
  x.content == y.content /\
  idx y >= idx x /\
  idx x + length x >= idx y + length y

let includes_live #a h (x: buffer a) (y: buffer a)
: Lemma
  (requires (x `includes` y))
  (ensures (live h x <==> live h y))
= ()

let includes_as_seq #a h1 h2 (x: buffer a) (y: buffer a)
: Lemma
  (requires (x `includes` y /\ as_seq h1 x == as_seq h2 x))
  (ensures (as_seq h1 y == as_seq h2 y))
= Seq.slice_slice (sel h1 x) (idx x) (idx x + length x) (idx y - idx x) (idx y  - idx x + length y);
  Seq.slice_slice (sel h2 x) (idx x) (idx x + length x) (idx y - idx x) (idx y  - idx x + length y)

let includes_trans #a (x y z: buffer a)
: Lemma
  (requires (x `includes` y /\ y `includes` z))
  (ensures (x `includes` z))
= ()

(* Disjointness between two buffers *)
let disjoint #a #a' (x:buffer a) (y:buffer a') : GTot Type0 =
  frameOf x =!= frameOf y \/ as_addr x =!= as_addr y
  \/ (a == a' /\ as_addr x == as_addr y /\ frameOf x == frameOf y /\ x.max_length == y.max_length /\
     (idx x + length x <= idx y \/ idx y + length y <= idx x))

(* Disjointness is symmetric *)
let lemma_disjoint_symm #a #a' (x:buffer a) (y:buffer a') : Lemma
  (requires True)
  (ensures (disjoint x y <==> disjoint y x))
  [SMTPat (disjoint x y)]
  = ()

let lemma_disjoint_sub #a #a' (x:buffer a) (subx:buffer a) (y:buffer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPatT (disjoint subx y); SMTPatT (includes x subx)]
  = ()

let lemma_disjoint_sub' #a #a' (x:buffer a) (subx:buffer a) (y:buffer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPatT (disjoint y subx); SMTPatT (includes x subx)]
  = ()

val lemma_live_disjoint: #a:Type -> #a':Type -> h:mem -> b:buffer a -> b':buffer a' -> Lemma
  (requires (live h b /\ b' `unused_in` h))
  (ensures (disjoint b b'))
  [SMTPatT (disjoint b b'); SMTPatT (live h b)]
let lemma_live_disjoint #a #a' h b b' = ()

(* Heterogeneous buffer type *)
noeq type abuffer = | Buff: #t:Type -> b:buffer t -> abuffer

(* let empty : TSet.set abuffer = TSet.empty #abuffer *)
let only #t (b:buffer t) : Tot (TSet.set abuffer) = FStar.TSet.singleton (Buff #t b)
(* let op_Plus_Plus #a s (b:buffer a) : Tot (TSet.set abuffer) = TSet.union s (only b) *)
(* let op_Plus_Plus_Plus set1 set2 : Tot (TSet.set abuffer) = FStar.TSet.union set1 set2 *)

let op_Bang_Bang = TSet.singleton
let op_Plus_Plus = TSet.union

(* Maps a set of buffer to the set of their references *)
assume val arefs: TSet.set abuffer -> Tot (Set.set nat)

assume Arefs_def: forall (x:nat) (s:TSet.set abuffer). {:pattern (Set.mem x (arefs s))}
  Set.mem x (arefs s) <==> (exists (y:abuffer). TSet.mem y s /\ as_addr y.b == x)

val lemma_arefs_1: s:TSet.set abuffer -> Lemma
  (requires (s == TSet.empty #abuffer))
  (ensures  (arefs s == Set.empty #nat))
  [SMTPat (arefs s)]
let lemma_arefs_1 s = Set.lemma_equal_intro (arefs s) (Set.empty)

val lemma_arefs_2: s1:TSet.set abuffer -> s2:TSet.set abuffer -> Lemma
  (requires True)
  (ensures  (arefs (s1 ++ s2) == Set.union (arefs s1) (arefs s2)))
  [SMTPatOr [
    [SMTPat (arefs (s2 ++ s1))];
    [SMTPat (arefs (s1 ++ s2))]
  ]]
let lemma_arefs_2 s1 s2 =
  Set.lemma_equal_intro (arefs (s1 ++ s2)) (Set.union (arefs s1) (arefs s2))

val lemma_arefs_3: s1:TSet.set abuffer -> s2:TSet.set abuffer -> Lemma
  (requires (TSet.subset s1 s2))
  (ensures  (Set.subset (arefs s1) (arefs s2)))
let lemma_arefs_3 s1 s2 = ()

(* General disjointness predicate between a buffer and a set of heterogeneous buffers *)
let disjoint_from_bufs #a (b:buffer a) (bufs:TSet.set abuffer) =
  forall b'. TSet.mem b' bufs ==> disjoint b b'.b

(* General disjointness predicate between a buffer and a set of heterogeneous references *)
let disjoint_from_refs #a (b:buffer a) (set:Set.set nat) =
  ~(Set.mem (as_addr b) set)


(* Similar but specialized disjointness predicates *)
let disjoint_1 a b = disjoint a b
let disjoint_2 a b b' = disjoint a b /\ disjoint a b'
let disjoint_3 a b b' b'' = disjoint a b /\ disjoint a b' /\ disjoint a b''
let disjoint_4 a b b' b'' b''' = disjoint a b /\ disjoint a b' /\ disjoint a b'' /\ disjoint a b'''
let disjoint_5 a b b' b'' b''' b'''' = disjoint a b /\ disjoint a b' /\ disjoint a b'' /\ disjoint a b''' /\ disjoint a b''''

let disjoint_ref_1 (#t:Type) a (r:reference t) = frameOf a =!= r.id \/ as_addr a =!= HS.as_addr r
let disjoint_ref_2 a r r' = disjoint_ref_1 a r /\ disjoint_ref_1 a r'
let disjoint_ref_3 a r r' r'' = disjoint_ref_1 a r /\ disjoint_ref_2 a r' r''
let disjoint_ref_4 a r r' r'' r''' = disjoint_ref_1 a r /\ disjoint_ref_3 a r' r'' r'''
let disjoint_ref_5 a r r' r'' r''' r'''' = disjoint_ref_1 a r /\ disjoint_ref_4 a r' r'' r''' r''''

val disjoint_only_lemma: #a:Type -> #a':Type -> b:buffer a -> b':buffer a' -> Lemma
  (requires (disjoint b b'))
  (ensures (disjoint_from_bufs b (only b')))
let disjoint_only_lemma #a #a' b b' = ()

(* Fully general modifies clause *)
let modifies_bufs_and_refs (bufs:TSet.set abuffer) (refs:Set.set nat) h h' : GTot Type0 =
  (forall rid. Set.mem rid (Map.domain h.h) ==>
    (HH.modifies_rref rid (Set.union (arefs bufs) refs) h.h h'.h
    /\ (forall (#a:Type) (b:buffer a). (frameOf b == rid /\ live h b /\ disjoint_from_bufs b bufs
      /\ disjoint_from_refs b refs) ==> equal h b h' b /\ live h' b)))

(* Fully general modifies clause for buffer sets *)
let modifies_buffers (bufs:TSet.set abuffer) h h' : GTot Type0 =
  (forall rid. Set.mem rid (Map.domain h.h) ==>
    (HH.modifies_rref rid (arefs bufs) h.h h'.h /\
      (forall (#a:Type) (b:buffer a). {:pattern (frameOf b == rid /\ live h b /\ disjoint_from_bufs b bufs)}
	(frameOf b == rid /\ live h b /\ disjoint_from_bufs b bufs ==> equal h b h' b /\ live h' b))))

(* General modifies clause for buffers only *)
let modifies_bufs rid buffs h h' =
  modifies_ref rid (arefs buffs) h h'
  /\ (forall (#a:Type) (b:buffer a). (frameOf b == rid /\ live h b /\ disjoint_from_bufs b buffs) ==> equal h b h' b /\ live h' b)

let modifies_none h h' =
  h'.tip == h.tip /\ HH.modifies Set.empty h.h h'.h

(* Specialized clauses for small numbers of buffers *)
let modifies_buf_0 rid h h' =
  modifies_ref rid (Set.empty #nat) h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb == rid /\ live h bb) ==> equal h bb h' bb /\ live h' bb)

let modifies_buf_1 (#t:Type) rid (b:buffer t) h h' = //would be good to drop the rid argument on these, since they can be computed from the buffers
  modifies_ref rid (Set.singleton (Heap.addr_of (as_ref b))) h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb == rid /\ live h bb /\ disjoint b bb) ==> equal h bb h' bb /\ live h' bb)

let to_set_2 (n1:nat) (n2:nat) :Set.set nat = Set.union (Set.singleton n1) (Set.singleton n2)

let modifies_buf_2 (#t:Type) (#t':Type) rid (b:buffer t) (b':buffer t') h h' =
  modifies_ref rid (to_set_2 (as_addr b) (as_addr b')) h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb == rid /\ live h bb /\ disjoint b bb /\ disjoint b' bb)
       ==> equal h bb h' bb /\ live h' bb)

let to_set_3 (n1:nat) (n2:nat) (n3:nat) :Set.set nat = Set.union (Set.union (Set.singleton n1) (Set.singleton n2)) (Set.singleton n3)

let modifies_buf_3 (#t:Type) (#t':Type) (#t'':Type) rid (b:buffer t) (b':buffer t') (b'':buffer t'') h h' =
  modifies_ref rid (to_set_3 (as_addr b) (as_addr b') (as_addr b'')) h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb == rid /\ live h bb /\ disjoint b bb /\ disjoint b' bb /\ disjoint b'' bb)
       ==> equal h bb h' bb /\ live h' bb)

let to_set_4 (n1:nat) (n2:nat) (n3:nat) (n4:nat) :Set.set nat =
  Set.union (Set.union (Set.union (Set.singleton n1) (Set.singleton n2)) (Set.singleton n3)) (Set.singleton n4)

let modifies_buf_4 (#t:Type) (#t':Type) (#t'':Type) (#t''':Type) rid (b:buffer t) (b':buffer t') (b'':buffer t'') (b''':buffer t''') h h' =
  modifies_ref rid (to_set_4 (as_addr b) (as_addr b') (as_addr b'') (as_addr b''')) h h'
  /\ (forall (#tt:Type) (bb:buffer tt). (frameOf bb == rid /\ live h bb /\ disjoint b bb /\ disjoint b' bb /\ disjoint b'' bb /\ disjoint b''' bb)
       ==> equal h bb h' bb /\ live h' bb)


(* General lemmas for the modifies_bufs clause *)
let lemma_modifies_bufs_trans rid bufs h0 h1 h2 :
  Lemma (requires (modifies_bufs rid bufs h0 h1 /\ modifies_bufs rid bufs h1 h2))
	(ensures (modifies_bufs rid bufs h0 h2))
	[SMTPatT (modifies_bufs rid bufs h0 h1); SMTPatT (modifies_bufs rid bufs h1 h2)]
 = ()

let lemma_modifies_bufs_sub rid bufs subbufs h0 h1 :
  Lemma
    (requires (TSet.subset subbufs bufs /\ modifies_bufs rid subbufs h0 h1))
    (ensures (modifies_bufs rid bufs h0 h1))
    [SMTPatT (modifies_bufs rid subbufs h0 h1); SMTPatT (TSet.subset subbufs bufs)]
 = ()

val lemma_modifies_bufs_subset: #a:Type -> #a':Type -> h0:mem -> h1:mem -> bufs:TSet.set abuffer -> b:buffer a -> b':buffer a' -> Lemma
  (requires (disjoint_from_bufs b (bufs ++ (only b')) ))
  (ensures  (disjoint_from_bufs b bufs))
  [SMTPatT (modifies_bufs h0.tip (bufs ++ (only b')) h0 h1); SMTPatT (live h0 b)]
let lemma_modifies_bufs_subset #a #a' h0 h1 bufs b b' = ()

val lemma_modifies_bufs_superset: #a:Type -> #a':Type -> h0:mem -> h1:mem -> bufs:TSet.set abuffer -> b:buffer a -> b':buffer a' -> Lemma
  (requires (b' `unused_in` h0 /\ live h0 b /\ disjoint_from_bufs b bufs))
  (ensures (disjoint_from_bufs b (bufs ++ (only b'))))
  [SMTPatT (modifies_bufs h0.tip bufs h0 h1); SMTPatT (b' `unmapped_in` h0); SMTPatT (live h0 b)]
let lemma_modifies_bufs_superset #a #a' h0 h1 bufs b b' = ()

(* Specialized lemmas *)
let modifies_trans_0_0 rid h0 h1 h2 :
  Lemma (requires (modifies_buf_0 rid h0 h1 /\ modifies_buf_0 rid h1 h2))
	(ensures (modifies_buf_0 rid h0 h2))
	[SMTPatT (modifies_buf_0 rid h0 h1); SMTPatT (modifies_buf_0 rid h1 h2)]
 = ()

let modifies_trans_1_0 rid b h0 h1 h2 :
  Lemma (requires (modifies_buf_1 rid b h0 h1 /\ modifies_buf_0 rid h1 h2))
	(ensures (modifies_buf_1 rid b h0 h2))
	[SMTPatT (modifies_buf_1 rid b h0 h1); SMTPatT (modifies_buf_0 rid h1 h2)]
 = ()

let modifies_trans_0_1 rid b h0 h1 h2 :
  Lemma (requires (modifies_buf_0 rid h0 h1 /\ modifies_buf_1 rid b h1 h2))
	(ensures (modifies_buf_1 rid b h0 h2))
	[SMTPatT (modifies_buf_0 rid h0 h1); SMTPatT (modifies_buf_1 rid b h1 h2)]
 = ()

let modifies_trans_1_1 rid b h0 h1 h2 :
  Lemma (requires (modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid b h1 h2))
	(ensures (modifies_buf_1 rid b h0 h2))
	[SMTPatT (modifies_buf_1 rid b h0 h1); SMTPatT (modifies_buf_1 rid b h1 h2)]
 = ()

let modifies_trans_1_1' rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid b' h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPatT (modifies_buf_1 rid b h0 h1); SMTPatT (modifies_buf_1 rid b' h1 h2)]
 = ()

let modifies_trans_2_0 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_0 rid h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPatT (modifies_buf_2 rid b b' h0 h1); SMTPatT (modifies_buf_0 rid h1 h2)]
 = ()

let modifies_trans_2_1 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_1 rid b h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPatT (modifies_buf_2 rid b b' h0 h1); SMTPatT (modifies_buf_1 rid b h1 h2)]
 = ()

let modifies_trans_2_1' rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_2 rid b' b h0 h1 /\ modifies_buf_1 rid b h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPatT (modifies_buf_2 rid b' b h0 h1); SMTPatT (modifies_buf_1 rid b h1 h2)]
 = ()

let modifies_trans_0_2 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_0 rid h0 h1 /\ modifies_buf_2 rid b b' h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPatT (modifies_buf_0 rid h0 h1); SMTPatT (modifies_buf_2 rid b b' h1 h2)]
 = ()

let modifies_trans_1_2 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_1 rid b h0 h1 /\ modifies_buf_2 rid b b' h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPatT (modifies_buf_1 rid b h0 h1); SMTPatT (modifies_buf_2 rid b b' h1 h2)]
 = ()

let modifies_trans_2_2 rid b b' h0 h1 h2 :
  Lemma (requires (modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_2 rid b b' h1 h2))
	(ensures (modifies_buf_2 rid b b' h0 h2))
	[SMTPatT (modifies_buf_2 rid b b' h0 h1); SMTPatT (modifies_buf_2 rid b b' h1 h2)]
 = ()

let modifies_trans_3_3 rid b b' b'' h0 h1 h2 :
  Lemma (requires (modifies_buf_3 rid b b' b'' h0 h1 /\ modifies_buf_3 rid b b' b'' h1 h2))
	(ensures (modifies_buf_3 rid b b' b'' h0 h2))
	[SMTPatT (modifies_buf_3 rid b b' b'' h0 h1); SMTPatT (modifies_buf_3 rid b b' b'' h1 h2)]
 = ()

let modifies_trans_4_4 rid b b' b'' b''' h0 h1 h2 :
  Lemma (requires (modifies_buf_4 rid b b' b'' b''' h0 h1 /\ modifies_buf_4 rid b b' b'' b''' h1 h2))
	(ensures (modifies_buf_4 rid b b' b'' b''' h0 h2))
	[SMTPatT (modifies_buf_4 rid b b' b'' b''' h0 h1); SMTPatT (modifies_buf_4 rid b b' b'' b''' h1 h2)]
 = ()

(* TODO: complete with specialized versions of every general lemma *)

(* Modifies clauses that do not change the shape of the HyperStack (h1.tip = h0.tip) *)
(* NB: those clauses are made abstract in order to make verification faster
   Lemmas follow to allow the programmer to make use of the real definition
   of those predicates in a general setting *)
abstract let modifies_0 h0 h1 =
  modifies_one h0.tip h0 h1
  /\ modifies_buf_0 h0.tip h0 h1
  /\ h0.tip == h1.tip

(* This one is very generic: it says
 * - some references have changed in the frame of b, but
 * - among all buffers in this frame, b is the only one that changed. *)
abstract let modifies_1 (#a:Type) (b:buffer a) h0 h1 =
  let rid = frameOf b in
  modifies_one rid h0 h1 /\ modifies_buf_1 rid b h0 h1

abstract let modifies_2_1 (#a:Type) (b:buffer a) h0 h1 =
  let rid = frameOf b in
  ((rid == h0.tip /\ modifies_buf_1 rid b h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid =!= h0.tip /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_0 h0.tip h0 h1 ))

abstract let modifies_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 =
  let rid = frameOf b in let rid' = frameOf b' in
  ((rid == rid' /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid =!= rid' /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 ))

abstract let modifies_3 (#a:Type) (#a':Type) (#a'':Type) (b:buffer a) (b':buffer a')  (b'':buffer a'') h0 h1 =
  let rid = frameOf b in let rid' = frameOf b' in let rid'' = frameOf b'' in
  ((rid == rid' /\ rid' == rid'' /\ modifies_buf_3 rid b b' b'' h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid == rid' /\ rid' =!= rid'' /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_1 rid'' b'' h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid'')) h0.h h1.h )
  \/ (rid =!= rid' /\ rid' == rid'' /\ modifies_buf_2 rid' b' b'' h0 h1 /\ modifies_buf_1 rid b h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid'')) h0.h h1.h )
  \/ (rid == rid'' /\ rid' =!= rid'' /\ modifies_buf_2 rid b b'' h0 h1 /\ modifies_buf_1 rid' b' h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h1.h )
  \/ (rid =!= rid' /\ rid' =!= rid'' /\ rid =!= rid''
      /\ HH.modifies_just (Set.union (Set.union (Set.singleton rid) (Set.singleton rid')) (Set.singleton rid'')) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_1 rid'' b'' h0 h1))

abstract let modifies_3_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 =
  let rid = frameOf b in let rid' = frameOf b' in
  ((rid == rid' /\ rid' == h0.tip /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid == rid' /\ rid' =!= h0.tip /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_0 h0.tip h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h )
  \/ (rid =!= rid' /\ rid == h0.tip /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid') (Set.singleton h0.tip)) h0.h h1.h )
  \/ (rid =!= rid' /\ rid' == h0.tip /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_1 rid b h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h )
  \/ (rid =!= rid' /\ rid' =!= h0.tip /\ rid =!= h0.tip
      /\ HH.modifies_just (Set.union (Set.union (Set.singleton rid) (Set.singleton rid')) (Set.singleton h0.tip)) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_0 h0.tip h0 h1))

abstract let modifies_region rid bufs h0 h1 =
  modifies_one rid h0 h1 /\ modifies_bufs rid bufs h0 h1

(* Lemmas introducing the 'modifies' predicates *)
let lemma_intro_modifies_0 h0 h1 : Lemma
  (requires (modifies_one h0.tip h0 h1
  /\ modifies_buf_0 h0.tip h0 h1
  /\ h0.tip == h1.tip))
  (ensures  (modifies_0 h0 h1))
  = ()

let lemma_intro_modifies_1 (#a:Type) (b:buffer a) h0 h1 : Lemma
  (requires (let rid = frameOf b in
  modifies_one rid h0 h1 /\ modifies_buf_1 rid b h0 h1))
  (ensures  (modifies_1 b h0 h1))
  = ()

let lemma_intro_modifies_2_1 (#a:Type) (b:buffer a) h0 h1 : Lemma
  (requires (let rid = frameOf b in
  ((rid == h0.tip /\ modifies_buf_1 rid b h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid =!= h0.tip /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_0 h0.tip h0 h1 ))))
  (ensures  (modifies_2_1 b h0 h1))
  = ()

let lemma_intro_modifies_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 : Lemma
  (requires (let rid = frameOf b in let rid' = frameOf b' in
  ((rid == rid' /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid =!= rid' /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 ))))
  (ensures  (modifies_2 b b' h0 h1))
  = ()

let lemma_intro_modifies_3 (#a:Type) (#a':Type) (#a'':Type) (b:buffer a) (b':buffer a')  (b'':buffer a'') h0 h1 : Lemma
  (requires (let rid = frameOf b in let rid' = frameOf b' in let rid'' = frameOf b'' in
  ((rid == rid' /\ rid' == rid'' /\ modifies_buf_3 rid b b' b'' h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid == rid' /\ rid' =!= rid'' /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_1 rid'' b'' h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid'')) h0.h h1.h )
  \/ (rid =!= rid' /\ rid' == rid'' /\ modifies_buf_2 rid' b' b'' h0 h1 /\ modifies_buf_1 rid b h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid'')) h0.h h1.h )
  \/ (rid == rid'' /\ rid' =!= rid'' /\ modifies_buf_2 rid b b'' h0 h1 /\ modifies_buf_1 rid' b' h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h1.h )
  \/ (rid =!= rid' /\ rid' =!= rid'' /\ rid =!= rid''
      /\ HH.modifies_just (Set.union (Set.union (Set.singleton rid) (Set.singleton rid')) (Set.singleton rid'')) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_1 rid'' b'' h0 h1))))
  (ensures  (modifies_3 b b' b'' h0 h1))
  = ()

let lemma_intro_modifies_3_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 : Lemma
  (requires (let rid = frameOf b in let rid' = frameOf b' in
  ((rid == rid' /\ rid' == h0.tip /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_one rid h0 h1)
  \/ (rid == rid' /\ rid' =!= h0.tip /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_0 h0.tip h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h )
  \/ (rid =!= rid' /\ rid == h0.tip /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid') (Set.singleton h0.tip)) h0.h h1.h )
  \/ (rid =!= rid' /\ rid' == h0.tip /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_1 rid b h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h )
  \/ (rid =!= rid' /\ rid' =!= h0.tip /\ rid =!= h0.tip
      /\ HH.modifies_just (Set.union (Set.union (Set.singleton rid) (Set.singleton rid')) (Set.singleton h0.tip)) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_0 h0.tip h0 h1))))
  (ensures  (modifies_3_2 b b' h0 h1))
  = ()

let lemma_intro_modifies_region rid bufs h0 h1 : Lemma
  (requires (modifies_one rid h0 h1 /\ modifies_bufs rid bufs h0 h1))
  (ensures  (modifies_region rid bufs h0 h1))
  = ()


(* Lemmas revealing the content of the specialized modifies clauses in order to
   be able to generalize them if needs be. *)
let lemma_reveal_modifies_0 h0 h1 : Lemma
  (requires (modifies_0 h0 h1))
  (ensures  (modifies_one h0.tip h0 h1 /\ modifies_buf_0 h0.tip h0 h1 /\ h0.tip == h1.tip))
  = ()

let lemma_reveal_modifies_1 (#a:Type) (b:buffer a) h0 h1 : Lemma
  (requires (modifies_1 b h0 h1))
  (ensures  (let rid = frameOf b in modifies_one rid h0 h1 /\ modifies_buf_1 rid b h0 h1))
  = ()

let lemma_reveal_modifies_2_1 (#a:Type) (b:buffer a) h0 h1 : Lemma
  (requires (modifies_2_1 b h0 h1))
  (ensures  (let rid = frameOf b in
    ((rid == h0.tip /\ modifies_buf_1 rid b h0 h1 /\ modifies_one rid h0 h1)
    \/ (rid =!= h0.tip /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_0 h0.tip h0 h1 ))))
  = ()

let lemma_reveal_modifies_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 : Lemma
  (requires (modifies_2 b b' h0 h1))
  (ensures  (let rid = frameOf b in let rid' = frameOf b' in
    ((rid == rid' /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_one rid h0 h1)
    \/ (rid =!= rid' /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h1.h
      /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 )) ))
  = ()

let lemma_reveal_modifies_3 (#a:Type) (#a':Type) (#a'':Type) (b:buffer a) (b':buffer a')  (b'':buffer a'') h0 h1 : Lemma
  (requires (modifies_3 b b' b'' h0 h1))
  (ensures  (let rid = frameOf b in let rid' = frameOf b' in let rid'' = frameOf b'' in
    ((rid == rid' /\ rid' == rid'' /\ modifies_buf_3 rid b b' b'' h0 h1 /\ modifies_one rid h0 h1)
    \/ (rid == rid' /\ rid' =!= rid'' /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_1 rid'' b'' h0 h1
	/\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid'')) h0.h h1.h )
	\/ (rid =!= rid' /\ rid' == rid'' /\ modifies_buf_2 rid' b' b'' h0 h1 /\ modifies_buf_1 rid b h0 h1
	/\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid'')) h0.h h1.h )
	\/ (rid == rid'' /\ rid' =!= rid'' /\ modifies_buf_2 rid b b'' h0 h1 /\ modifies_buf_1 rid' b' h0 h1
	/\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton rid')) h0.h h1.h )
	\/ (rid =!= rid' /\ rid' =!= rid'' /\ rid =!= rid''
	/\ HH.modifies_just (Set.union (Set.union (Set.singleton rid) (Set.singleton rid')) (Set.singleton rid'')) h0.h h1.h
	/\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_1 rid'' b'' h0 h1)) ))
  = ()

let lemma_reveal_modifies_3_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 : Lemma
  (requires (modifies_3_2 b b' h0 h1))
  (ensures  (let rid = frameOf b in let rid' = frameOf b' in
    ((rid == rid' /\ rid' == h0.tip /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_one rid h0 h1)
    \/ (rid == rid' /\ rid' =!= h0.tip /\ modifies_buf_2 rid b b' h0 h1 /\ modifies_buf_0 h0.tip h0 h1
      /\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h )
      \/ (rid =!= rid' /\ rid == h0.tip /\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1
	/\ HH.modifies_just (Set.union (Set.singleton rid') (Set.singleton h0.tip)) h0.h h1.h )
	\/ (rid =!= rid' /\ rid' == h0.tip /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_1 rid b h0 h1
	/\ HH.modifies_just (Set.union (Set.singleton rid) (Set.singleton h0.tip)) h0.h h1.h )
	\/ (rid =!= rid' /\ rid' =!= h0.tip /\ rid =!= h0.tip
	/\ HH.modifies_just (Set.union (Set.union (Set.singleton rid) (Set.singleton rid')) (Set.singleton h0.tip)) h0.h h1.h
	/\ modifies_buf_1 rid b h0 h1 /\ modifies_buf_1 rid' b' h0 h1 /\ modifies_buf_0 h0.tip h0 h1)) ))
  = ()

let lemma_reveal_modifies_region rid bufs h0 h1 : Lemma
  (requires (modifies_region rid bufs h0 h1))
  (ensures  (modifies_one rid h0 h1 /\ modifies_bufs rid bufs h0 h1))
  = ()

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --initial_fuel 0 --initial_ifuel 0"

(* Stack effect specific lemmas *)
let lemma_stack_1 (#a:Type) (b:buffer a) h0 h1 h2 h3 : Lemma
  (requires (live h0 b /\ fresh_frame h0 h1 /\ modifies_1 b h1 h2 /\ popped h2 h3))
  (ensures  (modifies_buf_1 (frameOf b) b h0 h3))
    [SMTPatT (modifies_1 b h1 h2); SMTPatT (fresh_frame h0 h1); SMTPatT (popped h2 h3)]
  = ()

let lemma_stack_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 h3 : Lemma
  (requires (live h0 b /\ live h0 b' /\ fresh_frame h0 h1 /\ modifies_2 b b' h1 h2 /\ popped h2 h3))
  (ensures  (modifies_2 b b' h0 h3))
  [SMTPatT (modifies_2 b b' h1 h2); SMTPatT (fresh_frame h0 h1); SMTPatT (popped h2 h3)]
  = ()

(* Specialized modifies clauses lemmas + associated SMTPatterns. Those are critical for
   verification as the specialized modifies clauses are abstract from outside the
   module *)

(** Commutativity lemmas *)
let lemma_modifies_2_comm (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 : Lemma
  (requires True)
  (ensures  (modifies_2 b b' h0 h1 <==> modifies_2 b' b h0 h1))
  [SMTPatT (modifies_2 b b' h0 h1)]
  = ()

let lemma_modifies_3_2_comm (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 : Lemma
  (requires True)
  (ensures  (modifies_3_2 b b' h0 h1 <==> modifies_3_2 b' b h0 h1))
  [SMTPatT (modifies_3_2 b b' h0 h1)]
  = ()
(* TODO: add commutativity lemmas for modifies_3 *)

#reset-options "--z3rlimit 20"

(** Transitivity lemmas *)
let lemma_modifies_0_trans h0 h1 h2 : Lemma
  (requires (modifies_0 h0 h1 /\ modifies_0 h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (modifies_0 h1 h2)]
  = ()

let lemma_modifies_1_trans (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (modifies_1 b h0 h1 /\ modifies_1 b h1 h2))
  (ensures (modifies_1 b h0 h2))
  [SMTPatT (modifies_1 b h0 h1); SMTPatT (modifies_1 b h1 h2)]
  = ()

let lemma_modifies_2_1_trans (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (modifies_2_1 b h0 h1 /\ modifies_2_1 b h1 h2))
  (ensures (modifies_2_1 b h0 h2))
  [SMTPatT (modifies_2_1 b h0 h1); SMTPatT (modifies_2_1 b h1 h2)]
  = ()

let lemma_modifies_2_trans (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (modifies_2 b b' h0 h1 /\ modifies_2 b b' h1 h2))
  (ensures  (modifies_2 b b' h0 h2))
  (* TODO: Make the following work and merge with the following lemma *)
  (* [SMTPatOr [ *)
  (*     [SMTPatT (modifies_2 b b' h0 h1); *)
  (*      SMTPatT (modifies_2 b' b h0 h1)]]; *)
  (*  SMTPatT (modifies_2 b' b h1 h2)] *)
  [SMTPatT (modifies_2 b b' h0 h1); SMTPatT (modifies_2 b b' h1 h2)]
  = ()

let lemma_modifies_2_trans' (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (modifies_2 b b' h0 h1 /\ modifies_2 b b' h1 h2))
  (ensures  (modifies_2 b b' h0 h2))
  [SMTPatT (modifies_2 b' b h0 h1); SMTPatT (modifies_2 b b' h1 h2)]
  = ()

#reset-options "--z3rlimit 40"

let lemma_modifies_3_trans (#a:Type) (#a':Type) (#a'':Type) (b:buffer a) (b':buffer a') (b'':buffer a'') h0 h1 h2 : Lemma
  (requires (modifies_3 b b' b'' h0 h1 /\ modifies_3 b b' b'' h1 h2))
  (ensures (modifies_3 b b' b'' h0 h2))
  (* TODO: add the appropriate SMTPatOr patterns so as not to rewrite X times the same lemma *)
  [SMTPatT (modifies_3 b b' b'' h0 h1); SMTPatT (modifies_3 b b' b'' h1 h2)]
  = ()

#reset-options "--z3rlimit 200"

let lemma_modifies_3_2_trans (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (modifies_3_2 b b' h0 h1 /\ modifies_3_2 b b' h1 h2))
  (ensures (modifies_3_2 b b' h0 h2))
  [SMTPatT (modifies_3_2 b b' h0 h1); SMTPatT (modifies_3_2 b b' h1 h2)]
  = ()
let lemma_modifies_3_2_trans' (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (modifies_3_2 b' b h0 h1 /\ modifies_3_2 b b' h1 h2))
  (ensures (modifies_3_2 b b' h0 h2))
  [SMTPatT (modifies_3_2 b' b h0 h1); SMTPatT (modifies_3_2 b b' h1 h2)]
  = ()

#reset-options "--z3rlimit 20"

(* Specific modifies clause lemmas *)
val lemma_modifies_0_0: h0:mem -> h1:mem -> h2:mem -> Lemma
  (requires (modifies_0 h0 h1 /\ modifies_0 h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (modifies_0 h1 h2)]
let lemma_modifies_0_0 h0 h1 h2 = ()

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

let lemma_modifies_1_0 (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (live h0 b /\ modifies_1 b h0 h1 /\ modifies_0 h1 h2))
  (ensures  (live h2 b /\ modifies_2_1 b h0 h2))
  [SMTPatT (modifies_1 b h0 h1); SMTPatT (modifies_0 h1 h2)]
  = ()

let lemma_modifies_0_1 (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (live h0 b /\ modifies_0 h0 h1 /\ modifies_1 b h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (modifies_1 b h1 h2)]
  = ()

let lemma_modifies_0_1' (#a:Type) (b:buffer a) h0 h1 h2 : Lemma
  (requires (b `unused_in` h0 /\ modifies_0 h0 h1 /\ live h1 b /\ modifies_1 b h1 h2))
  (ensures  (modifies_0 h0 h2))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (modifies_1 b h1 h2)]
  = ()

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

let lemma_modifies_1_1 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ modifies_1 b h0 h1 /\ modifies_1 b' h1 h2))
  (ensures  (modifies_2 b b' h0 h2 /\ modifies_2 b' b h0 h2))
  [SMTPatT (modifies_1 b h0 h1); SMTPatT (modifies_1 b' h1 h2)]
  = ()

#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0"

let lemma_modifies_0_2 (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ b' `unused_in` h0 /\ modifies_0 h0 h1 /\ live h1 b'
    /\ modifies_2 b b' h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPatT (modifies_2 b b' h1 h2); SMTPatT (modifies_0 h0 h1)]
  = ()

let lemma_modifies_0_2' (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ b' `unused_in` h0 /\ modifies_0 h0 h1 /\ live h1 b'
    /\ modifies_2 b' b h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPatT (modifies_2 b' b h1 h2); SMTPatT (modifies_0 h0 h1)]
  = ()

let lemma_modifies_1_2 (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ modifies_1 b h0 h1 /\ b' `unused_in` h0 /\ live h1 b' /\
    modifies_2 b b' h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPatT (modifies_1 b h0 h1); SMTPatT (modifies_2 b b' h1 h2)]
  = ()

let lemma_modifies_1_2' (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ modifies_1 b h0 h1 /\ b' `unused_in` h0 /\ live h1 b' /\
    modifies_2 b' b h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPatT (modifies_1 b h0 h1); SMTPatT (modifies_2 b' b h1 h2)]
  = ()

let lemma_modifies_1_2'' (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ modifies_1 b h0 h1 /\ modifies_2 b b' h1 h2))
  (ensures  (modifies_2 b b' h0 h2))
  [SMTPatT (modifies_1 b h0 h1); SMTPatT (modifies_2 b b' h1 h2)]
  = ()

let lemma_modifies_1_2''' (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ modifies_1 b h0 h1 /\ modifies_2 b' b h1 h2))
  (ensures  (modifies_2 b' b h0 h2))
  [SMTPatT (modifies_1 b h0 h1); SMTPatT (modifies_2 b' b h1 h2)]
  = ()

let lemma_modifies_1_1_prime (#t:Type) (#t':Type) (b:buffer t) (b':buffer t') h0 h1 h2 : Lemma
  (requires (live h0 b /\ modifies_1 b h0 h1 /\ b' `unused_in` h0 /\ live h1 b' /\
    modifies_1 b' h1 h2))
  (ensures  (modifies_2_1 b h0 h2))
  [SMTPatT (modifies_1 b h0 h1); SMTPatT (modifies_1 b' h1 h2)]
  = ()

let lemma_modifies_2_1 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ modifies_2 b b' h0 h1 /\ modifies_1 b h1 h2))
  (ensures  (modifies_2 b b' h0 h2))
  [SMTPatT (modifies_2 b b' h0 h1); SMTPatT (modifies_1 b h1 h2)]
  = ()

let lemma_modifies_2_1' (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ modifies_2 b' b h0 h1 /\ modifies_1 b h1 h2))
  (ensures  (modifies_2 b' b h0 h2))
  [SMTPatT (modifies_2 b' b h0 h1); SMTPatT (modifies_1 b h1 h2)]
  = ()

let lemma_modifies_2_1'' (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 h2 : Lemma
  (requires (live h0 b /\ live h0 b' /\ modifies_2_1 b h0 h1 /\ modifies_1 b' h1 h2))
  (ensures  (modifies_3_2 b b' h0 h2))
  [SMTPatT (modifies_2_1 b h0 h1); SMTPatT (modifies_1 b' h1 h2)]
  = ()

(* TODO: lemmas for modifies_3 *)

#reset-options "--initial_fuel 0 --max_fuel 0"

(** Concrete getters and setters *)
val create: #a:Type -> init:a -> len:UInt32.t -> StackInline (buffer a)
  (requires (fun h -> True))
  (ensures (fun (h0:mem) b h1 -> b `unused_in` h0
     /\ live h1 b /\ idx b == 0 /\ length b == v len
     /\ frameOf b == h0.tip
     /\ Map.domain h1.h == Map.domain h0.h
     /\ modifies_0 h0 h1
     /\ as_seq h1 b == Seq.create (v len) init))
let create #a init len =
  let content: reference (s:seq a{Seq.length s == v len}) =
     salloc (Seq.create (v len) init) in
  let b = MkBuffer len content 0ul len in
  let h = HST.get() in
  assert (Seq.equal (as_seq h b) (sel h b));
  b

#reset-options "--initial_fuel 0 --max_fuel 0"

unfold let p (#a:Type0) (init:list a) : GTot Type0 =
  normalize (0 < FStar.List.Tot.length init) /\
  normalize (FStar.List.Tot.length init < UInt.max_int 32)

unfold let q (#a:Type0) (len:nat) (buf:buffer a) : GTot Type0 =
  normalize (length buf == len)

(** Concrete getters and setters *)
val createL: #a:Type0 -> init:list a -> StackInline (buffer a)
  (requires (fun h -> p #a init))
  (ensures (fun (h0:mem) b h1 ->
     let len = FStar.List.Tot.length init in
     len > 0
     /\ b `unused_in` h0
     /\ live h1 b /\ idx b == 0 /\ length b == len
     /\ frameOf b == h0.tip
     /\ Map.domain h1.h == Map.domain h0.h
     /\ modifies_0 h0 h1
     /\ as_seq h1 b == Seq.of_list init
     /\ q #a len b))
#set-options "--initial_fuel 1 --max_fuel 1" //the normalize_term (length init) in the pre-condition will be unfolded
	                                     //whereas the L.length init below will not
let createL #a init =
  let len = UInt32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.of_list init in
  lemma_of_list_length s init;
  let content: reference (s:seq a{Seq.length s == v len}) =
    salloc (Seq.of_list init) in
  let b = MkBuffer len content 0ul len in
  let h = HST.get() in
  assert (Seq.equal (as_seq h b) (sel h b));
  b

#reset-options "--initial_fuel 0 --max_fuel 0"
let lemma_upd (#a:Type) (h:mem) (x:reference a{live_region h x.id}) (v:a) : Lemma
  (requires True)
  (ensures  (Map.domain h.h == Map.domain (upd h x v).h))
  = let m = h.h in
    let m' = Map.upd m x.id (Heap.upd (Map.sel m x.id) (HH.as_ref x.ref) v) in
    Set.lemma_equal_intro (Map.domain m) (Map.domain m')

val rcreate: #a:Type -> r:HH.rid -> init:a -> len:UInt32.t -> ST (buffer a)
  (requires (fun h -> is_eternal_region r))
  (ensures (fun (h0:mem) b h1 -> b `unused_in` h0
    /\ live h1 b /\ idx b == 0 /\ length b == v len
    /\ Map.domain h1.h == Map.domain h0.h
    /\ h1.tip == h0.tip
    /\ modifies (Set.singleton r) h0 h1
    /\ modifies_ref r Set.empty h0 h1
    /\ as_seq h1 b == Seq.create (v len) init
    /\ ~(is_mm b.content)))
let rcreate #a r init len =
  let h0 = HST.get() in
  let s = Seq.create (v len) init in
  let content: reference (s:seq a{Seq.length s == v len}) = ralloc r s in
  let b = MkBuffer len content 0ul len in
  let h1 = HST.get() in
  assert (Seq.equal (as_seq h1 b) (sel h1 b));
  lemma_upd h0 content s;
  b


(* #reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0" *)

(* val create_null: #a:Type -> init:a -> len:UInt32.t -> Stack (buffer a) *)
(*   (requires (fun h -> True)) *)
(*   (ensures (fun h0 b h1 -> length b = UInt32.v len /\ h0 == h1)) *)
(* let create_null #a init len = *)
(*   push_frame(); *)
(*   let r = create init len in *)
(*   pop_frame(); *)
(*   r *)


#reset-options "--initial_fuel 0 --max_fuel 0"

// ocaml-only, used for conversions to Platform.bytes
val to_seq: #a:Type -> b:buffer a -> l:UInt32.t{v l <= length b} -> STL (seq a)
  (requires (fun h -> live h b))
  (ensures  (fun h0 r h1 -> h0 == h1 /\ live h1 b /\ Seq.length r == v l
    (*/\ r == as_seq #a h1 b *) ))
let to_seq #a b l =
  let s = !b.content in
  let i = v b.idx in
  Seq.slice s i (i + v l)


// ocaml-only, used for conversions to Platform.bytes
val to_seq_full: #a:Type -> b:buffer a -> ST (seq a)
  (requires (fun h -> live h b))
  (ensures  (fun h0 r h1 -> h0 == h1 /\ live h1 b /\ 
			 r == as_seq #a h1 b ))
let to_seq_full #a b =
  let s = !b.content in
  let i = v b.idx in
  Seq.slice s i (i + v b.length)

val index: #a:Type -> b:buffer a -> n:UInt32.t{v n < length b} -> Stack a
  (requires (fun h -> live h b))
  (ensures (fun h0 z h1 -> live h0 b /\ h1 == h0
    /\ z == Seq.index (as_seq h0 b) (v n)))
let index #a b n =
  let s = !b.content in
  Seq.index s (v b.idx + v n)

(** REMARK: the proof of this lemma relies crucially on the `a == a'` condition
    in `disjoint`, and on the pattern in `Seq.slice_upd` *)
private let lemma_aux_0
  (#a:Type) (b:buffer a) (n:UInt32.t{v n < length b}) (z:a) (h0:mem) (tt:Type) (bb:buffer tt)
  :Lemma (requires (live h0 b /\ live h0 bb /\ disjoint b bb))
         (ensures  (live h0 b /\ live h0 bb /\
	            (let h1 = HS.upd h0 b.content (Seq.upd (sel h0 b) (idx b + v n) z) in
		     as_seq h0 bb == as_seq h1 bb)))
  = ()

#set-options "--z3rlimit 10"
private let lemma_aux_1
  (#a:Type) (b:buffer a) (n:UInt32.t{v n < length b}) (z:a) (h0:mem) (tt:Type)
  :Lemma (requires (live h0 b))
         (ensures  (live h0 b /\
	            (forall (bb:buffer tt). (live h0 bb /\ disjoint b bb) ==>
		                       (let h1 = HS.upd h0 b.content (Seq.upd (sel h0 b) (idx b + v n) z) in
		                        as_seq h0 bb == as_seq h1 bb))))
  = let open FStar.Classical in
    forall_intro (move_requires (lemma_aux_0 b n z h0 tt))

#reset-options "--initial_fuel 0 --max_fuel 0"

private let lemma_aux_2
  (#a:Type) (b:buffer a) (n:UInt32.t{v n < length b}) (z:a) (h0:mem)
  :Lemma (requires (live h0 b))
         (ensures  (live h0 b /\
	            (forall (tt:Type) (bb:buffer tt). (live h0 bb /\ disjoint b bb) ==>
		                                 (let h1 = HS.upd h0 b.content (Seq.upd (sel h0 b) (idx b + v n) z) in
		                                  as_seq h0 bb == as_seq h1 bb))))
  = let open FStar.Classical in
    forall_intro (move_requires (lemma_aux_1 b n z h0))

private val lemma_aux: #a:Type -> b:buffer a -> n:UInt32.t{v n < length b} -> z:a
  -> h0:mem -> Lemma
  (requires (live h0 b))
  (ensures (live h0 b
    /\ modifies_1 b h0 (HS.upd h0 b.content (Seq.upd (sel h0 b) (idx b + v n) z)) ))
  [SMTPat (HS.upd h0 b.content (Seq.upd (sel h0 b) (idx b + v n) z))]
let lemma_aux #a b n z h0 = lemma_aux_2 b n z h0

val upd: #a:Type -> b:buffer a -> n:UInt32.t -> z:a -> Stack unit
  (requires (fun h -> live h b /\ v n < length b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ v n < length b
    /\ modifies_1 b h0 h1
    /\ as_seq h1 b == Seq.upd (as_seq h0 b) (v n) z ))
let upd #a b n z =
  let h0 = HST.get () in
  let s0 = !b.content in
  let s = Seq.upd s0 (v b.idx + v n) z in
  b.content := s;
  lemma_aux b n z h0;
  let h = HST.get() in
  Seq.lemma_eq_intro (as_seq h b) (Seq.slice s (idx b) (idx b + length b));
  Seq.upd_slice s0 (idx b) (idx b + length b) (v n) z

val sub: #a:Type -> b:buffer a -> i:UInt32.t
  -> len:UInt32.t{v i + v len <= length b}
  -> Tot (b':buffer a{b `includes` b' /\ length b' == v len})
let sub #a b i len =
  assert (v i + v b.idx < pow2 n); // was formerly a precondition
  MkBuffer b.max_length b.content (i +^ b.idx) len

let sub_sub
  (#a: Type)
  (b: buffer a)
  (i1: UInt32.t)
  (len1: UInt32.t{v i1 + v len1 <= length b})
  (i2: UInt32.t)
  (len2: UInt32.t {v i2 + v len2 <= v len1})
: Lemma
  (ensures (sub (sub b i1 len1) i2 len2 == sub b (i1 +^ i2) len2))
= ()  

let sub_zero_length
  (#a: Type)
  (b: buffer a)
: Lemma
  (ensures (sub b (UInt32.uint_to_t 0) (UInt32.uint_to_t (length b)) == b))
= ()

let lemma_sub_spec (#a:Type) (b:buffer a)
  (i:UInt32.t)
  (len:UInt32.t{v len <= length b /\ v i + v len <= length b})
  h : Lemma
     (requires (live h b))
     (ensures  (live h (sub b i len) /\
                as_seq h (sub b i len) == Seq.slice (as_seq h b) (v i) (v i + v len)))
  [SMTPat (sub b i len); SMTPatT (live h b)]
  = Seq.lemma_eq_intro (as_seq h (sub b i len)) (Seq.slice (as_seq h b) (v i) (v i + v len))

let lemma_sub_spec' (#a:Type) (b:buffer a)
  (i:UInt32.t)
  (len:UInt32.t{v len <= length b /\ v i + v len <= length b})
  h : Lemma
     (requires (live h b))
     (ensures  (live h (sub b i len) /\
                as_seq h (sub b i len) == Seq.slice (as_seq h b) (v i) (v i + v len)))
  [SMTPatT (live h (sub b i len))]
  = lemma_sub_spec b i len h

val offset: #a:Type -> b:buffer a
  -> i:UInt32.t{v i + v b.idx < pow2 n /\ v i <= v b.length}
  -> Tot (b':buffer a{b `includes` b'})
let offset #a b i =
  MkBuffer b.max_length b.content (i +^ b.idx) (b.length -^ i)

let lemma_offset_spec (#a:Type) (b:buffer a)
  (i:UInt32.t{v i + v b.idx < pow2 n /\ v i <= v b.length})
  h : Lemma
     (requires True)
     (ensures  (as_seq h (offset b i) == Seq.slice (as_seq h b) (v i) (length b)))
     [SMTPatOr [[SMTPat (as_seq h (offset b i))];
                [SMTPat (Seq.slice (as_seq h b) (v i) (length b))]]]
  = Seq.lemma_eq_intro (as_seq h (offset b i)) (Seq.slice (as_seq h b) (v i) (length b))
  
private val eq_lemma1:
    #a:eqtype
  -> b1:buffer a
  -> b2:buffer a
  -> len:UInt32.t{v len <= length b1 /\ v len <= length b2}
  -> h:mem
  -> Lemma
    (requires (forall (j:nat). j < v len ==> get h b1 j == get h b2 j))
    (ensures  equal h (sub b1 0ul len) h (sub b2 0ul len))
    [SMTPatT (equal h (sub b1 0ul len) h (sub b2 0ul len))]
let eq_lemma1 #a b1 b2 len h =
  Seq.lemma_eq_intro (as_seq h (sub b1 0ul len)) (as_seq h (sub b2 0ul len))

#reset-options "--z3rlimit 20"

private val eq_lemma2:
    #a:eqtype
  -> b1:buffer a
  -> b2:buffer a
  -> len:UInt32.t{v len <= length b1 /\ v len <= length b2}
  -> h:mem
  -> Lemma
    (requires equal h (sub b1 0ul len) h (sub b2 0ul len))
    (ensures  (forall (j:nat). j < v len ==> get h b1 j == get h b2 j))
    [SMTPatT (equal h (sub b1 0ul len) h (sub b2 0ul len))]
let eq_lemma2 #a b1 b2 len h =
  let s1 = as_seq h (sub b1 0ul len) in
  let s2 = as_seq h (sub b2 0ul len) in
  cut (forall (j:nat). j < v len ==> get h b1 j == Seq.index s1 j);
  cut (forall (j:nat). j < v len ==> get h b2 j == Seq.index s2 j)

(** Corresponds to memcmp for `eqtype` *)
val eqb: #a:eqtype -> b1:buffer a -> b2:buffer a
  -> len:UInt32.t{v len <= length b1 /\ v len <= length b2}
  -> ST bool
    (requires (fun h -> live h b1 /\ live h b2))
    (ensures  (fun h0 z h1 -> h1 == h0 /\
      (z <==> equal h0 (sub b1 0ul len) h0 (sub b2 0ul len))))
let rec eqb #a b1 b2 len =
  if len =^ 0ul then true
  else
    let len' = len -^ 1ul in
    if index b1 len' = index b2 len' then
      eqb b1 b2 len'
    else
      false

(**
    Defining operators for buffer accesses as specified at
    https://github.com/FStarLang/FStar/wiki/Parsing-and-operator-precedence
   *)
(* JP: if the [val] is not specified, there's an issue with these functions
 * taking an extra unification parameter at extraction-time... *)
val op_Array_Access: #a:Type -> b:buffer a -> n:UInt32.t{v n<length b} -> Stack a
     (requires (fun h -> live h b))
     (ensures (fun h0 z h1 -> h1 == h0
       /\ z == Seq.index (as_seq h0 b) (v n)))
let op_Array_Access #a b n = index #a b n

val op_Array_Assignment: #a:Type -> b:buffer a -> n:UInt32.t -> z:a -> Stack unit
  (requires (fun h -> live h b /\ v n < length b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ v n < length b
    /\ modifies_1 b h0 h1
    /\ as_seq h1 b == Seq.upd (as_seq h0 b) (v n) z ))
let op_Array_Assignment #a b n z = upd #a b n z

let lemma_modifies_one_trans_1 (#a:Type) (b:buffer a) (h0:mem) (h1:mem) (h2:mem): Lemma
  (requires (modifies_one (frameOf b) h0 h1 /\ modifies_one (frameOf b) h1 h2))
  (ensures (modifies_one (frameOf b) h0 h2))
  [SMTPatT (modifies_one (frameOf b) h0 h1); SMTPatT (modifies_one (frameOf b) h1 h2)]
  = ()

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --initial_fuel 0 --initial_ifuel 0"

(** Corresponds to memcpy *)
val blit: #t:Type
  -> a:buffer t
  -> idx_a:UInt32.t{v idx_a <= length a}
  -> b:buffer t{disjoint a b}
  -> idx_b:UInt32.t{v idx_b <= length b}
  -> len:UInt32.t{v idx_a + v len <= length a /\ v idx_b + v len <= length b}
  -> Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures  (fun h0 _ h1 -> live h0 b /\ live h0 a /\ live h1 b /\ live h1 a /\ modifies_1 b h0 h1
      /\ Seq.slice (as_seq h1 b) (v idx_b) (v idx_b + v len) ==
        Seq.slice (as_seq h0 a) (v idx_a) (v idx_a + v len)
      /\ Seq.slice (as_seq h1 b) 0 (v idx_b) ==
        Seq.slice (as_seq h0 b) 0 (v idx_b)
      /\ Seq.slice (as_seq h1 b) (v idx_b+v len) (length b) ==
        Seq.slice (as_seq h0 b) (v idx_b+v len) (length b) ))
let rec blit #t a idx_a b idx_b len =
  let h0 = HST.get () in
  if len =^ 0ul then ()
  else
    begin
    let len' = len -^ 1ul in
    blit #t a idx_a b idx_b len';
    let z = a.(idx_a +^ len') in
    b.(idx_b +^ len') <- z;
    let h1 = HST.get() in
    Seq.snoc_slice_index (as_seq h1 b) (v idx_b) (v idx_b + v len');
    Seq.cons_head_tail (Seq.slice (as_seq h0 b) (v idx_b + v len') (length b));
    Seq.cons_head_tail (Seq.slice (as_seq h1 b) (v idx_b + v len') (length b))
    end

(** Corresponds to memset *)
val fill: #t:Type
  -> b:buffer t
  -> z:t
  -> len:UInt32.t{v len <= length b}
  -> Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
      /\ Seq.slice (as_seq h1 b) 0 (v len) == Seq.create (v len) z
      /\ Seq.slice (as_seq h1 b) (v len) (length b) ==
        Seq.slice (as_seq h0 b) (v len) (length b) ))
let rec fill #t b z len =
  let h0 = HST.get () in
  if len =^ 0ul then ()
  else
    begin
    let len' = len -^ 1ul in
    fill #t b z len';
    b.(len') <- z;
    let h = HST.get() in
    Seq.snoc_slice_index (as_seq h b) 0 (v len');
    Seq.lemma_tail_slice (as_seq h b) (v len') (length b)
    end;
  let h1 = HST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h1 b) 0 (v len)) (Seq.create (v len) z)


let split #t (b:buffer t) (i:UInt32.t{v i <= length b}) : Tot (buffer t * buffer t)
  = sub b 0ul i, offset b i

let join #t (b:buffer t) (b':buffer t{b.max_length == b'.max_length /\ b.content == b'.content /\ idx b + length b == idx b'}) : Tot (buffer t)
  = MkBuffer (b.max_length) (b.content) (b.idx) (FStar.UInt32.(b.length +^ b'.length))


val no_upd_lemma_0: #t:Type -> h0:mem -> h1:mem -> b:buffer t -> Lemma
  (requires (live h0 b /\ modifies_0 h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPatT (modifies_0 h0 h1); SMTPatT (live h0 b)]
let no_upd_lemma_0 #t h0 h1 b = ()

val no_upd_lemma_1: #t:Type -> #t':Type -> h0:mem -> h1:mem -> a:buffer t -> b:buffer t' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ modifies_1 a h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPatT (modifies_1 a h0 h1); SMTPatT (live h0 b)]
let no_upd_lemma_1 #t #t' h0 h1 a b = ()

#reset-options "--z3rlimit 30 --initial_fuel 0 --max_fuel 0"

val no_upd_lemma_2: #t:Type -> #t':Type -> #t'':Type -> h0:mem -> h1:mem -> a:buffer t -> a':buffer t' -> b:buffer t'' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ disjoint a' b /\ modifies_2 a a' h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPatT (live h0 b); SMTPatT (modifies_2 a a' h0 h1)]
let no_upd_lemma_2 #t #t' #t'' h0 h1 a a' b = ()

val no_upd_lemma_2_1: #t:Type -> #t':Type -> h0:mem -> h1:mem -> a:buffer t -> b:buffer t' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ modifies_2_1 a h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPatT (live h0 b); SMTPatT (modifies_2_1 a h0 h1)]
let no_upd_lemma_2_1 #t #t' h0 h1 a b = ()

val no_upd_fresh: #t:Type -> h0:mem -> h1:mem -> a:buffer t -> Lemma
  (requires (live h0 a /\ fresh_frame h0 h1))
  (ensures  (live h0 a /\ live h1 a /\ equal h0 a h1 a))
  [SMTPatT (live h0 a); SMTPatT (fresh_frame h0 h1)]
let no_upd_fresh #t h0 h1 a = ()

val no_upd_popped: #t:Type -> h0:mem -> h1:mem -> b:buffer t -> Lemma
  (requires (live h0 b /\ frameOf b =!= h0.tip /\ popped h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPatT (live h0 b); SMTPatT (popped h0 h1)]
let no_upd_popped #t h0 h1 b = ()

(* Modifies of subset lemmas *)
let lemma_modifies_sub_0 h0 h1 : Lemma
  (requires (h1 == h0))
  (ensures  (modifies_0 h0 h1))
  [SMTPatT (modifies_0 h0 h1)]
  = ()

let lemma_modifies_sub_1 #t h0 h1 (b:buffer t) : Lemma
  (requires (h1 == h0))
  (ensures  (modifies_1 b h0 h1))
  [SMTPatT (live h0 b); SMTPatT (modifies_1 b h0 h1)]
  = ()

let lemma_modifies_sub_2 #t #t' h0 h1 (b:buffer t) (b':buffer t') : Lemma
  (requires (h1 == h0))
  (ensures  (modifies_2 b b' h0 h1))
  [SMTPatT (live h0 b); SMTPatT (live h0 b'); SMTPatT (modifies_2 b b' h0 h1)]
  = ()

let lemma_modifies_sub_2_1 #t h0 h1 (b:buffer t) : Lemma
  (requires (modifies_0 h0 h1 /\ live h0 b))
  (ensures  (modifies_2_1 b h0 h1))
  [SMTPatT (live h0 b); SMTPatT (modifies_2_1 b h0 h1)]
  = ()

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

let modifies_subbuffer_1 (#t:Type) h0 h1 (sub:buffer t) (a:buffer t) : Lemma
  (requires (live h0 a /\ modifies_1 sub h0 h1 /\ includes a sub))
  (ensures  (modifies_1 a h0 h1 /\ live h1 a))
  [SMTPatT (modifies_1 sub h0 h1); SMTPatT (includes a sub)]
  = ()

let modifies_subbuffer_2 (#t:Type) (#t':Type) h0 h1 (sub:buffer t) (a':buffer t') (a:buffer t) : Lemma
  (requires (live h0 a /\ live h0 a' /\ includes a sub /\ modifies_2 sub a' h0 h1 ))
  (ensures  (modifies_2 a a' h0 h1 /\ modifies_2 a' a h0 h1 /\ live h1 a))
  [SMTPatT (modifies_2 sub a' h0 h1); SMTPatT (includes a sub)]
  = ()
    
let modifies_subbuffer_2' (#t:Type) (#t':Type) h0 h1 (sub:buffer t) (a':buffer t') (a:buffer t) : Lemma
  (requires (live h0 a /\ live h0 a' /\ includes a sub /\ modifies_2 a' sub h0 h1 ))
  (ensures  (modifies_2 a a' h0 h1 /\ live h1 a))
  [SMTPatT (modifies_2 a' sub h0 h1); SMTPatT (includes a sub)]
  = ()

let modifies_subbuffer_2_1 (#t:Type) h0 h1 (sub:buffer t) (a:buffer t) : Lemma
  (requires (live h0 a /\ includes a sub /\ modifies_2_1 sub h0 h1))
  (ensures  (modifies_2_1 a h0 h1 /\ live h1 a))
  [SMTPatT (modifies_2_1 sub h0 h1); SMTPatT (includes a sub)]
  = ()

let modifies_subbuffer_2_prime (#t:Type) h0 h1 (sub1:buffer t) (sub2:buffer t) (a:buffer t) : Lemma
  (requires (live h0 a /\ includes a sub1 /\ includes a sub2 /\ modifies_2 sub1 sub2 h0 h1))
  (ensures  (modifies_1 a h0 h1 /\ live h1 a))
  [SMTPatT (modifies_2 sub1 sub2 h0 h1); SMTPatT (includes a sub1); SMTPatT (includes a sub2)]
  = ()

let modifies_popped_3_2 (#t:Type) #t' (a:buffer t) (b:buffer t') h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ live h0 b /\ fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_3_2 a b h1 h2))
  (ensures  (modifies_2 a b h0 h3))
  [SMTPatT (fresh_frame h0 h1); SMTPatT (popped h2 h3); SMTPatT (modifies_3_2 a b h1 h2)]
  = ()

let modifies_popped_2 (#t:Type) #t' (a:buffer t) (b:buffer t') h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ live h0 b /\ fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_2 a b h1 h2))
  (ensures  (modifies_2 a b h0 h3))
  [SMTPatT (fresh_frame h0 h1); SMTPatT (popped h2 h3); SMTPatT (modifies_2 a b h1 h2)]
  = ()

let modifies_popped_1 (#t:Type) (a:buffer t) h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_2_1 a h1 h2))
  (ensures  (modifies_1 a h0 h3))
  [SMTPatT (fresh_frame h0 h1); SMTPatT (popped h2 h3); SMTPatT (modifies_2_1 a h1 h2)]
  = ()

let modifies_popped_1' (#t:Type) (a:buffer t) h0 h1 h2 h3 : Lemma
  (requires (live h0 a /\ fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_1 a h1 h2))
  (ensures  (modifies_1 a h0 h3))
  [SMTPatT (fresh_frame h0 h1); SMTPatT (popped h2 h3); SMTPatT (modifies_1 a h1 h2)]
  = ()

let modifies_popped_0 h0 h1 h2 h3 : Lemma
  (requires (fresh_frame h0 h1 /\ popped h2 h3 /\ modifies_0 h1 h2))
  (ensures  (modifies_0 h0 h3))
  [SMTPatT (fresh_frame h0 h1); SMTPatT (popped h2 h3); SMTPatT (modifies_0 h1 h2)]
  = ()

let live_popped (#t:Type) (b:buffer t) h0 h1 : Lemma
  (requires (popped h0 h1 /\ live h0 b /\ frameOf b =!= h0.tip))
  (ensures  (live h1 b))
  [SMTPatT (popped h0 h1); SMTPatT (live h0 b)]
  = ()

let live_fresh (#t:Type) (b:buffer t) h0 h1 : Lemma
  (requires (fresh_frame h0 h1 /\ live h0 b))
  (ensures  (live h1 b))
  [SMTPatT (fresh_frame h0 h1); SMTPatT (live h0 b)]
  = ()

let modifies_0_to_2_1_lemma (#t:Type) h0 h1 (b:buffer t) : Lemma
  (requires (modifies_0 h0 h1 /\ live h0 b))
  (ensures  (modifies_2_1 b h0 h1))
  [SMTPatT (modifies_2_1 b h0 h1); SMTPatT (live h0 b) ]
  = ()

let lemma_modifies_none_push_pop h0 h1 h2 : Lemma
  (requires (fresh_frame h0 h1 /\ popped h1 h2))
  (ensures  (modifies_none h0 h2))
  = ()

let lemma_modifies_0_push_pop h0 h1 h2 h3 : Lemma
  (requires (fresh_frame h0 h1 /\ modifies_0 h1 h2 /\ popped h2 h3))
  (ensures  (modifies_none h0 h3))
  = ()

let modifies_1_to_2_1_lemma (#t:Type) h0 h1 (b:buffer t) : Lemma
  (requires (modifies_1 b h0 h1 /\ live h0 b))
  (ensures  (modifies_2_1 b h0 h1))
  [SMTPatT (modifies_2_1 b h0 h1); SMTPatT (live h0 b) ]
  = ()

(* let modifies_1_to_2_lemma (#t:Type) #t' h0 h1 (b:buffer t) (b':buffer t'): Lemma *)
(*   (requires (modifies_1 b h0 h1 /\ live h0 b)) *)
(*   (ensures  (modifies_2 b b' h0 h1)) *)
(*   [SMTPatT (modifies_2 b b' h0 h1); SMTPatT (live h0 b) ] *)
(*   = () *)

let modifies_poppable_0 h0 h1 : Lemma
  (requires (modifies_0 h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPatT (modifies_0 h0 h1)]
  = ()

let modifies_poppable_1 #t h0 h1 (b:buffer t) : Lemma
  (requires (modifies_1 b h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPatT (modifies_1 b h0 h1)]
  = ()

let modifies_poppable_2_1 #t h0 h1 (b:buffer t) : Lemma
  (requires (modifies_2_1 b h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPatT (modifies_2_1 b h0 h1)]
  = ()

let modifies_poppable_2 #t #t' h0 h1 (b:buffer t) (b':buffer t') : Lemma
  (requires (modifies_2 b b' h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPatT (modifies_2 b' b h0 h1)]
  = ()

let modifies_poppable_3_2 #t #t' h0 h1 (b:buffer t) (b':buffer t') : Lemma
  (requires (modifies_3_2 b b' h0 h1 /\ HS.poppable h0))
  (ensures  (HS.poppable h1))
  [SMTPatT (modifies_3_2 b' b h0 h1)]
  = ()

let lemma_fresh_poppable h0 h1 : Lemma
  (requires (fresh_frame h0 h1))
  (ensures  (poppable h1))
  [SMTPatT (fresh_frame h0 h1)]
  = ()

let lemma_equal_domains_popped h0 h1 h2 h3 : Lemma
  (requires (equal_domains h0 h1 /\ popped h0 h2 /\ popped h1 h3))
  (ensures  (equal_domains h2 h3))
  = ()

let lemma_equal_domains h0 h1 h2 h3 : Lemma
  (requires (fresh_frame h0 h1 /\ equal_domains h1 h2 /\ popped h2 h3))
  (ensures  (equal_domains h0 h3))
  [SMTPatT (fresh_frame h0 h1); SMTPatT (equal_domains h1 h2); SMTPatT (popped h2 h3)]
  = ()

let lemma_equal_domains_2 h0 h1 h2 h3 h4 : Lemma
  (requires (fresh_frame h0 h1
    /\ modifies_0 h1 h2 /\ Map.domain h1.h == Map.domain h2.h
    /\ equal_domains h2 h3 /\ popped h3 h4))
  (ensures  (equal_domains h0 h4))
  [SMTPatT (fresh_frame h0 h1); SMTPatT (modifies_0 h1 h2); SMTPatT (popped h3 h4)]
  = ()
