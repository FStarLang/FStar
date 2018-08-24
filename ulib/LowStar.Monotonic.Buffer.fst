module LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

private let replace_subseq (#a:Type0)
  (s:Seq.seq a) (offset:nat) (len:nat{offset + len <= Seq.length s}) (sub:Seq.lseq a len)
  :Tot (Seq.seq a)
  = Seq.replace_subseq s offset (offset + len) sub

private let lemma_replace_subseq_elim (#a:Type0)
  (s:Seq.seq a) (offset:nat) (len:nat{offset + len <= Seq.length s}) (sub:Seq.lseq a len)
  :Lemma (let s1 = replace_subseq s offset len sub in
          Seq.length s1 == Seq.length s /\
          Seq.equal (Seq.slice s1 0 offset) (Seq.slice s 0 offset) /\
	  Seq.equal (Seq.slice s1 offset (offset + len)) sub /\
	  Seq.equal (Seq.slice s1 (offset + len) (Seq.length s1)) (Seq.slice s (offset + len) (Seq.length s)))
	 [SMTPat (replace_subseq s offset len sub)]
  = ()

private let srel_to_lsrel (#a:Type0) (len:nat) (pre:srel a) :P.preorder (Seq.lseq a len) = fun s1 s2 -> pre s1 s2

noeq type mbuffer (a:Type0) (rrel:srel a) (rel:srel a) :Type0 =
  | Null
  | Buffer:
    max_length:U32.t ->
    content:HST.mreference (Seq.lseq a (U32.v max_length)) (srel_to_lsrel (U32.v max_length) rrel) ->
    idx:U32.t ->
    length:U32.t{U32.v idx + U32.v length <= U32.v max_length} ->
    compatible:squash (compatible_sub_preorder (U32.v max_length) rrel
                                               (U32.v idx) (U32.v idx + U32.v length) rel) ->  //proof of compatibility
    mbuffer a rrel rel

let g_is_null #_ #_ #_ b = Null? b

let mnull #_ #_ #_ = Null

let null_unique #_ #_ #_ _ = ()

let unused_in #_ #_ #_ b h =
  match b with
  | Null -> False
  | Buffer _ content _ _ _ -> content `HS.unused_in` h

let live #_ #_ #_ h b =
  match b with
  | Null -> True
  | Buffer _ content _ _ _ -> h `HS.contains` content

let live_null _ _ _ _ = ()

let live_not_unused_in #_ #_ #_ _ _ = ()

let frameOf #_ #_ #_ b = if Null? b then HS.root else HS.frameOf (Buffer?.content b)

let as_addr #_ #_ #_  b = if g_is_null b then 0 else HS.as_addr (Buffer?.content b)

let unused_in_equiv #_ #_ #_ b h =
  if g_is_null b then Heap.not_addr_unused_in_nullptr (Map.sel (HS.get_hmap h) HS.root) else ()

let live_region_frameOf #_ #_ #_ _ _ = ()

let len #_ #_ #_ b =
  match b with
  | Null -> 0ul
  | Buffer _ _ _ len _ -> len

let len_null a _ _ = ()

let as_seq #_ #_ #_ h b =
  match b with
  | Null -> Seq.empty
  | Buffer max_len content idx len _ ->
    Seq.slice (HS.sel h content) (U32.v idx) (U32.v idx + U32.v len)

let length_as_seq #_ #_ #_ _ _ = ()

(*
 * Reflexivity of the compatibility relation
 *)
let lemma_seq_sub_compatilibity_is_reflexive (#a:Type0) (len:nat) (rel:srel a)
  :Lemma (compatible_sub_preorder len rel 0 len rel)
  = assert (forall (s1 s2:Seq.seq a). Seq.length s1 == Seq.length s2 ==> Seq.equal (Seq.replace_subseq s1 0 (Seq.length s1) s2) s2)

(*
 * Transitivity of the compatibility relation
 *
 * i2 and j2 are offsets within [i1, j1) (i.e. assuming i1 = 0)
 *)
let lemma_seq_sub_compatibility_is_transitive (#a:Type0)
  (len:nat) (rel:srel a) (i1 j1:nat) (rel1:srel a) (i2 j2:nat) (rel2:srel a)
  :Lemma (requires (i1 <= j1 /\ j1 <= len /\ i2 <= j2 /\ j2 <= j1 - i1 /\
                    compatible_sub_preorder len rel i1 j1 rel1 /\
                    compatible_sub_preorder (j1 - i1) rel1 i2 j2 rel2))
	 (ensures  (compatible_sub_preorder len rel (i1 + i2) (i1 + j2) rel2))
  = let aux (a:Type0) (len i1 j1 i2 j2:nat) (s:Seq.seq a) (s2:Seq.seq a)
      :Lemma ((i1 <= j1 /\ j1 <= len /\ i2 <= j2 /\ j2 <= j1 - i1 /\ Seq.length s == len /\ Seq.length s2 == j2 - i2) ==>
	      (Seq.equal (Seq.replace_subseq s (i1 + i2) (i1 + j2) s2)
	                 (Seq.replace_subseq s i1 j1 (Seq.replace_subseq (Seq.slice s i1 j1) i2 j2 s2))))
      = ()
    in
    Classical.forall_intro_2 (aux a len i1 j1 i2 j2)

let mgsub #a #rrel #rel b i len sub_rel =
  match b with
  | Null -> Null
  | Buffer max_len content idx length () ->
    lemma_seq_sub_compatibility_is_transitive (U32.v max_len) rrel
                                              (U32.v idx) (U32.v idx + U32.v length) rel
		         	              (U32.v i) (U32.v i + U32.v len) sub_rel;
    Buffer max_len content (U32.add idx i) len ()

let live_gsub #_ #_ #_ _ _ _ _ _ = ()

let gsub_is_null #_ #_ #_ _ _ _ _ = ()

let len_gsub #_ #_ #_ _ _ _ _ = ()

let frameOf_gsub #_ #_ #_ _ _ _ _ = ()

let as_addr_gsub #_ #_ #_ _ _ _ _ = ()

let mgsub_inj #_ #_ #_ _ _ _ _ _ _ _ _ = ()

let gsub_gsub #_ #_ #rel b i1 len1 sub_rel1 i2 len2 sub_rel2 =
  lemma_seq_sub_compatibility_is_transitive (length b) rel (U32.v i1) (U32.v i1 + U32.v len1) sub_rel1
                                            (U32.v i2) (U32.v i2 + U32.v len2) sub_rel2


/// A buffer ``b`` is equal to its "largest" sub-buffer, at index 0 and
/// length ``len b``.

let gsub_zero_length #_ #_ #rel b = lemma_seq_sub_compatilibity_is_reflexive (length b) rel

let as_seq_gsub #_ #_ #_ h b i len _ =
  match b with
  | Null -> ()
  | Buffer _ content idx len0 _ ->
    Seq.slice_slice (HS.sel h content) (U32.v idx) (U32.v idx + U32.v len0) (U32.v i) (U32.v i + U32.v len)

(* Untyped view of buffers, used only to implement the generic modifies clause. DO NOT USE in client code. *)

noeq
type ubuffer_
: Type0
= {
  b_max_length: nat;
  b_offset: nat;
  b_length: nat;
  b_is_mm: bool;
}

val ubuffer' (region: HS.rid) (addr: nat) : Tot Type0

let ubuffer' region addr = (x: ubuffer_ { x.b_offset + x.b_length <= x.b_max_length } )

let ubuffer (region: HS.rid) (addr: nat) : Tot Type0 = G.erased (ubuffer' region addr)

let ubuffer_of_buffer' (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel)
  :Tot (ubuffer (frameOf b) (as_addr b))
  = if Null? b
    then
      Ghost.hide ({
        b_max_length = 0;
        b_offset = 0;
        b_length = 0;
        b_is_mm = false;
      })
    else
      Ghost.hide ({
        b_max_length = U32.v (Buffer?.max_length b);
        b_offset = U32.v (Buffer?.idx b);
        b_length = U32.v (Buffer?.length b);
       b_is_mm = HS.is_mm (Buffer?.content b);
    })

let ubuffer_preserved' 
  (#r: HS.rid)
  (#a: nat)
  (b: ubuffer r a)
  (h h' : HS.mem)
: GTot Type0
= forall (t':Type0) (rrel rel:srel t') (b':mbuffer t' rrel rel) .
  (frameOf b' == r /\ as_addr b' == a /\ ubuffer_of_buffer' b' == b /\ live h b') ==>
  (live h' b' /\ Seq.equal (as_seq h' b') (as_seq h b'))

val ubuffer_preserved (#r: HS.rid) (#a: nat) (b: ubuffer r a) (h h' : HS.mem) : GTot Type0

let ubuffer_preserved = ubuffer_preserved'

let ubuffer_preserved_intro
  (#r:HS.rid)
  (#a:nat)
  (b:ubuffer r a)
  (h h' :HS.mem)
  (f: (
    (t':Type0) ->
    (rrel:srel t') -> (rel:srel t') ->
    (b':mbuffer t' rrel rel) ->
    Lemma
    (requires (frameOf b' == r /\ as_addr b' == a /\ ubuffer_of_buffer' b' == b /\ live h b'))
    (ensures (live h' b' /\ as_seq h' b' == as_seq h b'))
  ))
: Lemma
  (ubuffer_preserved b h h')
= let g'
    (t':Type0) (rrel rel:srel t')
    (b':mbuffer t' rrel rel)
  : Lemma
    ((
      frameOf b' == r /\ as_addr b' == a /\ ubuffer_of_buffer' b' == b /\ live h b'
    ) ==> (
      live h' b' /\ as_seq h' b' == as_seq h b'
    ))
  = Classical.move_requires (f t' rrel rel) b'
  in
  Classical.forall_intro_4 g'

val ubuffer_preserved_refl (#r: HS.rid) (#a: nat) (b: ubuffer r a) (h : HS.mem) : Lemma
  (ubuffer_preserved b h h)

let ubuffer_preserved_refl #r #a b h = ()

val ubuffer_preserved_trans (#r: HS.rid) (#a: nat) (b: ubuffer r a) (h1 h2 h3 : HS.mem) : Lemma
  (requires (ubuffer_preserved b h1 h2 /\ ubuffer_preserved b h2 h3))
  (ensures (ubuffer_preserved b h1 h3))

let ubuffer_preserved_trans #r #a b h1 h2 h3 = ()

val same_mreference_ubuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: ubuffer r a)
  (h1 h2: HS.mem)
  (f: (
    (a' : Type) ->
    (pre: Preorder.preorder a') ->
    (r': HS.mreference a' pre) ->
    Lemma
    (requires (h1 `HS.contains` r' /\ r == HS.frameOf r' /\ a == HS.as_addr r'))
    (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
  ))
: Lemma
  (ubuffer_preserved b h1 h2)

let same_mreference_ubuffer_preserved #r #a b h1 h2 f =
  ubuffer_preserved_intro b h1 h2 (fun t' _ _ b' ->
    if Null? b'
    then ()
    else
      f _ _ (Buffer?.content b')
  )

val addr_unused_in_ubuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: ubuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.live_region h1 r ==> a `Heap.addr_unused_in` (Map.sel (HS.get_hmap h1) r)))
  (ensures (ubuffer_preserved b h1 h2))

let addr_unused_in_ubuffer_preserved #r #a b h1 h2 = ()

val ubuffer_of_buffer (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) :Tot (ubuffer (frameOf b) (as_addr b))

let ubuffer_of_buffer #_ #_ #_ b = ubuffer_of_buffer' b

val ubuffer_preserved_elim (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h h':HS.mem)
  :Lemma (requires (ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h' /\ live h b))
         (ensures (live h' b /\ as_seq h b == as_seq h' b))

let ubuffer_preserved_elim #_ #_ #_ _ _ _ = ()

let unused_in_ubuffer_preserved (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h h':HS.mem)
  : Lemma (requires (b `unused_in` h))
          (ensures (ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h'))
  = Classical.move_requires (fun b -> live_not_unused_in h b) b;
    live_null a rrel rel h;
    null_unique b;
    unused_in_equiv b h;
    addr_unused_in_ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h'

let ubuffer_includes' (larger smaller: ubuffer_) : GTot Type0 =
  larger.b_is_mm == smaller.b_is_mm /\
  larger.b_max_length == smaller.b_max_length /\
  larger.b_offset <= smaller.b_offset /\
  smaller.b_offset + smaller.b_length <= larger.b_offset + larger.b_length

(* TODO: added this because of #606, now that it is fixed, we may not need it anymore *)
let ubuffer_includes0 (#r1 #r2:HS.rid) (#a1 #a2:nat) (larger:ubuffer r1 a1) (smaller:ubuffer r2 a2) =
  r1 == r2 /\ a1 == a2 /\ ubuffer_includes' (G.reveal larger) (G.reveal smaller)

val ubuffer_includes (#r: HS.rid) (#a: nat) (larger smaller: ubuffer r a) : GTot Type0

let ubuffer_includes #r #a larger smaller = ubuffer_includes0 larger smaller
  
val ubuffer_includes_refl (#r: HS.rid) (#a: nat) (b: ubuffer r a) : Lemma
  (b `ubuffer_includes` b)

let ubuffer_includes_refl #r #a b = ()

val ubuffer_includes_trans (#r: HS.rid) (#a: nat) (b1 b2 b3: ubuffer r a) : Lemma
  (requires (b1 `ubuffer_includes` b2 /\ b2 `ubuffer_includes` b3))
  (ensures (b1 `ubuffer_includes` b3))

let ubuffer_includes_trans #r #a b1 b2 b3 = ()

(*
 * TODO: not sure how to make this lemma work with preorders
 *       it creates a buffer larger' in the proof
 *       we need a compatible preorder for that
 *       may be take that as an argument?
 *)
(*val ubuffer_includes_ubuffer_preserved (#r: HS.rid) (#a: nat) (larger smaller: ubuffer r a) (h1 h2: HS.mem) : Lemma
  (requires (larger `ubuffer_includes` smaller /\ ubuffer_preserved larger h1 h2))
  (ensures (ubuffer_preserved smaller h1 h2))
let ubuffer_includes_ubuffer_preserved #r #a larger smaller h1 h2 =
  ubuffer_preserved_intro smaller h1 h2 (fun t' b' ->
    if Null? b'
    then ()
    else
      let (Buffer max_len content idx' len') = b' in
      let idx = U32.uint_to_t (G.reveal larger).b_offset in
      let len = U32.uint_to_t (G.reveal larger).b_length in
      let larger' = Buffer max_len content idx len in
      assert (b' == gsub larger' (U32.sub idx' idx) len');
      ubuffer_preserved_elim larger' h1 h2
  )*)

let ubuffer_disjoint' (x1 x2: ubuffer_) : GTot Type0 =
  (x1.b_max_length == x2.b_max_length /\
    (x1.b_offset + x1.b_length <= x2.b_offset \/
     x2.b_offset + x2.b_length <= x1.b_offset))

(* TODO: added this because of #606, now that it is fixed, we may not need it anymore *)
let ubuffer_disjoint0 (#r1 #r2:HS.rid) (#a1 #a2:nat) (b1:ubuffer r1 a1) (b2:ubuffer r2 a2) =
  r1 == r2 /\ a1 == a2 /\
  ubuffer_disjoint' (G.reveal b1) (G.reveal b2)

val ubuffer_disjoint (#r:HS.rid) (#a:nat) (b1 b2:ubuffer r a) :GTot Type0
let ubuffer_disjoint #r #a b1 b2 = ubuffer_disjoint0 b1 b2

val ubuffer_disjoint_sym (#r:HS.rid) (#a: nat) (b1 b2:ubuffer r a)
  :Lemma (ubuffer_disjoint b1 b2 <==> ubuffer_disjoint b2 b1)
let ubuffer_disjoint_sym #_ #_ b1 b2 = ()

val ubuffer_disjoint_includes (#r: HS.rid) (#a: nat) (larger1 larger2: ubuffer r a) (smaller1 smaller2: ubuffer r a) : Lemma
  (requires (ubuffer_disjoint larger1 larger2 /\ larger1 `ubuffer_includes` smaller1 /\ larger2 `ubuffer_includes` smaller2))
  (ensures (ubuffer_disjoint smaller1 smaller2))

let ubuffer_disjoint_includes #r #a larger1 larger2 smaller1 smaller2 = ()

val liveness_preservation_intro (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (h h':HS.mem) (b:mbuffer a rrel rel)
  (f: (
    (t':Type0) ->
    (pre: Preorder.preorder t') ->
    (r: HS.mreference t' pre) ->
    Lemma
    (requires (HS.frameOf r == frameOf b /\ HS.as_addr r == as_addr b /\ h `HS.contains` r))
    (ensures (h' `HS.contains` r))
  ))
  :Lemma (requires (live h b)) (ensures (live h' b))

let liveness_preservation_intro #_ #_ #_ _ _ b f =
  if Null? b
  then ()
  else f _ _ (Buffer?.content b)

(* Basic, non-compositional modifies clauses, used only to implement the generic modifies clause. DO NOT USE in client code *)

let modifies_0_preserves_mreferences (h1 h2: HS.mem) : GTot Type0 =
  forall (a: Type) (pre: Preorder.preorder a) (r: HS.mreference a pre) .
  h1 `HS.contains` r ==> (h2 `HS.contains` r /\ HS.sel h1 r == HS.sel h2 r)

let modifies_0_preserves_regions (h1 h2: HS.mem) : GTot Type0 =
  forall (r: HS.rid) . HS.live_region h1 r ==> HS.live_region h2 r

let modifies_0_preserves_not_unused_in (h1 h2: HS.mem) : GTot Type0 =
  forall (r: HS.rid) (n: nat) . (
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)  
  ) ==> (
    n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)
  )

let modifies_0' (h1 h2: HS.mem) : GTot Type0 =
  modifies_0_preserves_mreferences h1 h2 /\
  modifies_0_preserves_regions h1 h2 /\
  modifies_0_preserves_not_unused_in h1 h2

val modifies_0 (h1 h2: HS.mem) : GTot Type0

let modifies_0 = modifies_0'

val modifies_0_live_region (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_0 h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

let modifies_0_live_region h1 h2 r = ()

val modifies_0_mreference (#a: Type) (#pre: Preorder.preorder a) (h1 h2: HS.mem) (r: HS.mreference a pre) : Lemma
  (requires (modifies_0 h1 h2 /\ h1 `HS.contains` r))
  (ensures (h2 `HS.contains` r /\ h1 `HS.sel` r == h2 `HS.sel` r))

let modifies_0_mreference #a #pre h1 h2 r = ()

let modifies_0_ubuffer
  (#r: HS.rid)
  (#a: nat)
  (b: ubuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_0 h1 h2))
  (ensures (ubuffer_preserved b h1 h2))
= same_mreference_ubuffer_preserved b h1 h2 (fun a' pre r' -> modifies_0_mreference h1 h2 r')

val modifies_0_unused_in
  (h1 h2: HS.mem)
  (r: HS.rid)
  (n: nat)
: Lemma
  (requires (
    modifies_0 h1 h2 /\
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)
  ))
  (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))

let modifies_0_unused_in h1 h2 r n = ()

let modifies_1_preserves_mreferences (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  :GTot Type0
  = forall (a':Type) (pre:Preorder.preorder a') (r':HS.mreference  a' pre).
      ((frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r') ==>
      (h2 `HS.contains` r' /\ HS.sel h1 r' == HS.sel h2 r')

let modifies_1_preserves_ubuffers (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  : GTot Type0
  = forall (b':ubuffer (frameOf b) (as_addr b)).
      (ubuffer_disjoint #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) b') ==> ubuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2

let modifies_1_preserves_livenesses (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  : GTot Type0
  = forall (a':Type) (pre:Preorder.preorder a') (r':HS.mreference  a' pre). h1 `HS.contains` r' ==> h2 `HS.contains` r'

let modifies_1' (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  : GTot Type0
  = modifies_0_preserves_regions h1 h2 /\
    modifies_1_preserves_mreferences b h1 h2 /\
    modifies_1_preserves_livenesses b h1 h2 /\
    modifies_0_preserves_not_unused_in h1 h2 /\
    modifies_1_preserves_ubuffers b h1 h2

val modifies_1 (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) :GTot Type0

let modifies_1 = modifies_1'

val modifies_1_live_region (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid)
  :Lemma (requires (modifies_1 b h1 h2 /\ HS.live_region h1 r)) (ensures (HS.live_region h2 r))

let modifies_1_live_region #_ #_ #_ _ _ _ _ = ()

val modifies_1_liveness
  (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r':HS.mreference a' pre)
  :Lemma (requires (modifies_1 b h1 h2 /\ h1 `HS.contains` r')) (ensures (h2 `HS.contains` r'))

let modifies_1_liveness #_ #_ #_ _ _ _ #_ #_ _ = ()

val modifies_1_unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid) (n:nat)
  :Lemma (requires (modifies_1 b h1 h2 /\
                    HS.live_region h1 r /\ HS.live_region h2 r /\
                    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)))
         (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))
let modifies_1_unused_in #_ #_ #_ _ _ _ _ _ = ()

val modifies_1_mreference
  (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r': HS.mreference a' pre)
  : Lemma (requires (modifies_1 b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
          (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
let modifies_1_mreference #_ #_ #_ _ _ _ #_ #_ _ = ()

val modifies_1_ubuffer (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem) (b':ubuffer (frameOf b) (as_addr b))
  : Lemma (requires (modifies_1 b h1 h2 /\ ubuffer_disjoint #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) b'))
          (ensures  (ubuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2))
let modifies_1_ubuffer #_ #_ #_ _ _ _ _ = ()

val modifies_1_null (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  : Lemma (requires (modifies_1 b h1 h2 /\ g_is_null b))
          (ensures  (modifies_0 h1 h2))
let modifies_1_null #_ #_ #_ _ _ _ = ()

let modifies_addr_of_preserves_not_unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  :GTot Type0
  = forall (r: HS.rid) (n: nat) .
      ((r <> frameOf b \/ n <> as_addr b) /\
       HS.live_region h1 r /\ HS.live_region h2 r /\
       n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)) ==>
      (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r))

let modifies_addr_of' (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) :GTot Type0 =
  modifies_0_preserves_regions h1 h2 /\
  modifies_1_preserves_mreferences b h1 h2 /\
  modifies_addr_of_preserves_not_unused_in b h1 h2

val modifies_addr_of (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) :GTot Type0
let modifies_addr_of = modifies_addr_of'

val modifies_addr_of_live_region (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid)
  :Lemma (requires (modifies_addr_of b h1 h2 /\ HS.live_region h1 r))
         (ensures (HS.live_region h2 r))
let modifies_addr_of_live_region #_ #_ #_ _ _ _ _ = ()

val modifies_addr_of_mreference (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r':HS.mreference a' pre)
  : Lemma (requires (modifies_addr_of b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
          (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
let modifies_addr_of_mreference #_ #_ #_ _ _ _ #_ #_ _ = ()

val modifies_addr_of_unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid) (n:nat)
  : Lemma (requires (modifies_addr_of b h1 h2 /\
                     (r <> frameOf b \/ n <> as_addr b) /\
                     HS.live_region h1 r /\ HS.live_region h2 r /\
                     n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)))
          (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))
let modifies_addr_of_unused_in #_ #_ #_ _ _ _ _ _ = ()

module MG = FStar.ModifiesGen

let cls : MG.cls ubuffer = MG.Cls #ubuffer
  ubuffer_includes
  (fun #r #a x -> ubuffer_includes_refl x)
  (fun #r #a x1 x2 x3 -> ubuffer_includes_trans x1 x2 x3)
  ubuffer_disjoint
  (fun #r #a x1 x2 -> ubuffer_disjoint_sym x1 x2)
  (fun #r #a larger1 larger2 smaller1 smaller2 -> ubuffer_disjoint_includes larger1 larger2 smaller1 smaller2)
  ubuffer_preserved
  (fun #r #a x h -> ubuffer_preserved_refl x h)
  (fun #r #a x h1 h2 h3 -> ubuffer_preserved_trans x h1 h2 h3)
  (fun #r #a b h1 h2 f -> same_mreference_ubuffer_preserved b h1 h2 f)

let loc = MG.loc cls

let loc_none = MG.loc_none

let loc_union = MG.loc_union

let loc_union_idem = MG.loc_union_idem

let loc_union_comm = MG.loc_union_comm

let loc_union_assoc = MG.loc_union_assoc

let loc_union_loc_none_l = MG.loc_union_loc_none_l

let loc_union_loc_none_r = MG.loc_union_loc_none_r

let loc_buffer #_ #_ #_ b =
  if g_is_null b then MG.loc_none
  else MG.loc_of_aloc #_ #_ #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let loc_buffer_null _ _ _ = ()

let loc_addresses = MG.loc_addresses

let loc_regions = MG.loc_regions

let loc_includes = MG.loc_includes

let loc_includes_refl = MG.loc_includes_refl

let loc_includes_trans = MG.loc_includes_trans

let loc_includes_union_r = MG.loc_includes_union_r

let loc_includes_union_l = MG.loc_includes_union_l

let loc_includes_none = MG.loc_includes_none

val loc_includes_buffer (#a:Type0) (#rrel1:srel a) (#rrel2:srel a) (#rel1:srel a) (#rel2:srel a)
  (b1:mbuffer a rrel1 rel1) (b2:mbuffer a rrel2 rel2)
  :Lemma (requires (frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2 /\
                    ubuffer_includes0 #(frameOf b1) #(frameOf b2) #(as_addr b1) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)))
         (ensures  (loc_includes (loc_buffer b1) (loc_buffer b2)))
let loc_includes_buffer #t #_ #_ #_ #_ b1 b2 =
  let t1 = ubuffer (frameOf b1) (as_addr b1) in
  MG.loc_includes_aloc #_ #cls #(frameOf b1) #(as_addr b1) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2 <: t1)

let loc_includes_gsub_buffer_r l #_ #_ #_ b i len sub_rel =
  let b' = mgsub b i len sub_rel in
  loc_includes_buffer b b';
  loc_includes_trans l (loc_buffer b) (loc_buffer b')

let loc_includes_gsub_buffer_l #_ #_ #rel b i1 len1 sub_rel1 i2 len2 sub_rel2 =
  let b1 = mgsub b i1 len1 sub_rel1 in
  let b2 = mgsub b i2 len2 sub_rel2 in
  loc_includes_buffer b1 b2

#push-options "--z3rlimit 20"
let loc_includes_as_seq #_ #rrel1 #rrel2 #_ #_ h1 h2 larger smaller =
  if Null? smaller then () else
  if Null? larger then begin
    MG.loc_includes_none_elim (loc_buffer smaller);
    MG.loc_of_aloc_not_none #_ #cls #(frameOf smaller) #(as_addr smaller) (ubuffer_of_buffer smaller)
  end else begin
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller);
    assume (rrel1 == rrel2);  //TODO: we should be able to prove this somehow in HS?
    let ul = Ghost.reveal (ubuffer_of_buffer larger) in
    let us = Ghost.reveal (ubuffer_of_buffer smaller) in
    assert (as_seq h1 smaller == Seq.slice (as_seq h1 larger) (us.b_offset - ul.b_offset) (us.b_offset - ul.b_offset + length smaller));
    assert (as_seq h2 smaller == Seq.slice (as_seq h2 larger) (us.b_offset - ul.b_offset) (us.b_offset - ul.b_offset + length smaller))
  end
#pop-options

let loc_includes_addresses_buffer #_ #_ #_ preserve_liveness r s p =
  MG.loc_includes_addresses_aloc #_ #cls preserve_liveness r s #(as_addr p) (ubuffer_of_buffer p)

let loc_includes_region_buffer #_ #_ #_ preserve_liveness s b =
  MG.loc_includes_region_aloc #_ #cls preserve_liveness s #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let loc_includes_region_addresses = MG.loc_includes_region_addresses #_ #cls

let loc_includes_region_region = MG.loc_includes_region_region #_ #cls

let loc_includes_region_union_l = MG.loc_includes_region_union_l

let loc_includes_addresses_addresses = MG.loc_includes_addresses_addresses cls

let loc_disjoint = MG.loc_disjoint

let loc_disjoint_sym = MG.loc_disjoint_sym

let loc_disjoint_none_r = MG.loc_disjoint_none_r

let loc_disjoint_union_r = MG.loc_disjoint_union_r

let loc_disjoint_includes = MG.loc_disjoint_includes

val loc_disjoint_buffer (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires ((frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2) ==>
                    ubuffer_disjoint0 #(frameOf b1) #(frameOf b2) #(as_addr b1) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)))
         (ensures (loc_disjoint (loc_buffer b1) (loc_buffer b2)))
let loc_disjoint_buffer #_ #_ #_ #_ #_ #_ b1 b2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)

let loc_disjoint_gsub_buffer #_ #_ #_ b i1 len1 sub_rel1 i2 len2 sub_rel2 =
  loc_disjoint_buffer (mgsub b i1 len1 sub_rel1) (mgsub b i2 len2 sub_rel2)

let loc_disjoint_addresses = MG.loc_disjoint_addresses_intro #_ #cls

let loc_disjoint_regions = MG.loc_disjoint_regions #_ #cls

let modifies = MG.modifies

let modifies_live_region = MG.modifies_live_region

let modifies_mreference_elim = MG.modifies_mreference_elim

let modifies_buffer_elim #_ #_ #_ b p h h' =
  if g_is_null b
  then
    assert (as_seq h b `Seq.equal` as_seq h' b)
  else begin
    MG.modifies_aloc_elim #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) p h h' ;
    ubuffer_preserved_elim b h h'
  end

let modifies_refl = MG.modifies_refl

let modifies_loc_includes = MG.modifies_loc_includes

let address_liveness_insensitive_locs = MG.address_liveness_insensitive_locs _

let region_liveness_insensitive_locs = MG.region_liveness_insensitive_locs _

let address_liveness_insensitive_buffer #_ #_ #_ b =
  MG.loc_includes_address_liveness_insensitive_locs_aloc #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let address_liveness_insensitive_addresses =
  MG.loc_includes_address_liveness_insensitive_locs_addresses cls

let region_liveness_insensitive_buffer #_ #_ #_ b =
  MG.loc_includes_region_liveness_insensitive_locs_loc_of_aloc #_ cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let region_liveness_insensitive_addresses =
  MG.loc_includes_region_liveness_insensitive_locs_loc_addresses cls

let region_liveness_insensitive_regions =
  MG.loc_includes_region_liveness_insensitive_locs_loc_regions cls

let region_liveness_insensitive_address_liveness_insensitive =
  MG.loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs cls

let modifies_liveness_insensitive_mreference = MG.modifies_preserves_liveness

let modifies_liveness_insensitive_buffer l1 l2 h h' #_ #_ #_ x =
  if g_is_null x then ()
  else
    liveness_preservation_intro h h' x (fun t' pre r ->
      MG.modifies_preserves_liveness_strong l1 l2 h h' r (ubuffer_of_buffer x))

let modifies_liveness_insensitive_region = MG.modifies_preserves_region_liveness

let modifies_liveness_insensitive_region_mreference = MG.modifies_preserves_region_liveness_reference

let modifies_liveness_insensitive_region_buffer l1 l2 h h' #_ #_ #_ x =
  if g_is_null x then ()
  else MG.modifies_preserves_region_liveness_aloc l1 l2 h h' #(frameOf x) #(as_addr x) (ubuffer_of_buffer x)

let modifies_trans = MG.modifies_trans

let modifies_only_live_regions = MG.modifies_only_live_regions

let no_upd_fresh_region = MG.no_upd_fresh_region

let fresh_frame_modifies = MG.fresh_frame_modifies #_ cls

let new_region_modifies = MG.new_region_modifies #_ cls

let popped_modifies = MG.popped_modifies #_ cls

let modifies_fresh_frame_popped = MG.modifies_fresh_frame_popped

let modifies_loc_regions_intro = MG.modifies_loc_regions_intro #_ #cls

let modifies_loc_addresses_intro = MG.modifies_loc_addresses_intro #_ #cls

let modifies_ralloc_post = MG.modifies_ralloc_post #_ #cls

let modifies_salloc_post = MG.modifies_salloc_post #_ #cls

let modifies_free = MG.modifies_free #_ #cls

let modifies_none_modifies = MG.modifies_none_modifies #_ #cls

let modifies_upd = MG.modifies_upd #_ #cls

val modifies_0_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_0 h1 h2))
  (ensures (modifies loc_none h1 h2))
let modifies_0_modifies h1 h2 =
  MG.modifies_none_intro #_ #cls h1 h2
    (fun r -> modifies_0_live_region h1 h2 r)
    (fun t pre b -> modifies_0_mreference #t #pre h1 h2 b)
    (fun r n -> modifies_0_unused_in h1 h2 r n)

val modifies_1_modifies
  (#a:Type0)(#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  :Lemma (requires (modifies_1 b h1 h2))
         (ensures  (modifies (loc_buffer b) h1 h2))
let modifies_1_modifies #t #_ #_ b h1 h2 =
  if g_is_null b
  then begin
    modifies_1_null b h1 h2;
    modifies_0_modifies h1 h2
  end else
   MG.modifies_intro (loc_buffer b) h1 h2
    (fun r -> modifies_1_live_region b h1 h2 r)
    (fun t pre p ->
      loc_disjoint_sym (loc_mreference p) (loc_buffer b);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) true (HS.frameOf p) (Set.singleton (HS.as_addr p));
      modifies_1_mreference b h1 h2 p
    )
    (fun t pre p ->
      modifies_1_liveness b h1 h2 p
    )
    (fun r n ->
      modifies_1_unused_in b h1 h2 r n
    )
    (fun r' a' b' ->
      loc_disjoint_sym (MG.loc_of_aloc b') (loc_buffer b);
      MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b) #(as_addr b)  #r' #a' (ubuffer_of_buffer b)  b';
      if frameOf b = r' && as_addr b = a'
      then
        modifies_1_ubuffer #t b h1 h2 b'
      else
        same_mreference_ubuffer_preserved #r' #a' b' h1 h2
          (fun a_ pre_ r_ -> modifies_1_mreference b h1 h2 r_)
    )

val modifies_addr_of_modifies
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  :Lemma (requires (modifies_addr_of b h1 h2))
         (ensures  (modifies (loc_addr_of_buffer b) h1 h2))
let modifies_addr_of_modifies #t #_ #_ b h1 h2 =
  MG.modifies_address_intro #_ #cls (frameOf b) (as_addr b) h1 h2
    (fun r -> modifies_addr_of_live_region b h1 h2 r)
    (fun t pre p ->
      modifies_addr_of_mreference b h1 h2 p
    )
    (fun r n ->
      modifies_addr_of_unused_in b h1 h2 r n
    )

let does_not_contain_addr = MG.does_not_contain_addr

let not_live_region_does_not_contain_addr = MG.not_live_region_does_not_contain_addr

let unused_in_does_not_contain_addr = MG.unused_in_does_not_contain_addr

let addr_unused_in_does_not_contain_addr = MG.addr_unused_in_does_not_contain_addr

let free_does_not_contain_addr = MG.free_does_not_contain_addr

let does_not_contain_addr_elim = MG.does_not_contain_addr_elim

let modifies_only_live_addresses = MG.modifies_only_live_addresses

let loc_not_unused_in = MG.loc_not_unused_in _

let loc_unused_in = MG.loc_unused_in _

let loc_unused_in_not_unused_in_disjoint =
  MG.loc_unused_in_not_unused_in_disjoint cls

let not_live_region_loc_not_unused_in_disjoint = MG.not_live_region_loc_not_unused_in_disjoint cls

let live_loc_not_unused_in #_ #_ #_ b h =
  unused_in_equiv b h;
  Classical.move_requires (MG.does_not_contain_addr_addr_unused_in h) (frameOf b, as_addr b);
  MG.loc_addresses_not_unused_in cls (frameOf b) (Set.singleton (as_addr b)) h;
  ()

let unused_in_loc_unused_in #_ #_ #_ b h =
  unused_in_equiv b h;
  Classical.move_requires (MG.addr_unused_in_does_not_contain_addr h) (frameOf b, as_addr b);
  MG.loc_addresses_unused_in cls (frameOf b) (Set.singleton (as_addr b)) h;
  ()

let modifies_address_liveness_insensitive_unused_in =
  MG.modifies_address_liveness_insensitive_unused_in cls

let modifies_only_not_unused_in = MG.modifies_only_not_unused_in

let mreference_live_loc_not_unused_in =
  MG.mreference_live_loc_not_unused_in cls

let mreference_unused_in_loc_unused_in =
  MG.mreference_unused_in_loc_unused_in cls

(* Duplicate the modifies clause to cope with cases that must not be used with transitivity *)

let modifies_inert = modifies

let modifies_inert_intro s h1 h2 = ()

let modifies_inert_live_region = modifies_live_region

let modifies_inert_mreference_elim = modifies_mreference_elim

let modifies_inert_buffer_elim = modifies_buffer_elim

let modifies_inert_liveness_insensitive_mreference_weak = modifies_liveness_insensitive_mreference_weak

let modifies_inert_liveness_insensitive_buffer_weak = modifies_liveness_insensitive_buffer_weak

let modifies_inert_liveness_insensitive_region_weak = modifies_liveness_insensitive_region_weak

let modifies_inert_liveness_insensitive_region_mreference_weak = modifies_liveness_insensitive_region_mreference_weak

let modifies_inert_liveness_insensitive_region_buffer_weak = modifies_liveness_insensitive_region_buffer_weak

let fresh_frame_modifies_inert = fresh_frame_modifies

let popped_modifies_inert = popped_modifies

let modifies_inert_loc_unused_in l h1 h2 l' =
  modifies_loc_includes address_liveness_insensitive_locs h1 h2 l;
  modifies_address_liveness_insensitive_unused_in h1 h2;
  loc_includes_trans (loc_unused_in h1) (loc_unused_in h2) l'

let disjoint_neq #_ #_ #_ #_ #_ #_ b1 b2 =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2 then
    MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)
  else ()
let includes_live #a #rrel #rel1 #rel2 h larger smaller =
  if Null? larger || Null? smaller then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)

let includes_frameOf_as_addr #_ #_ #_ #_ #_ #_ larger smaller =
  if Null? larger || Null? smaller then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)

let pointer_distinct_sel_disjoint #a #_ #_ #_ #_ b1 b2 h =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2
  then begin
    HS.mreference_distinct_sel_disjoint h (Buffer?.content b1) (Buffer?.content b2);
    loc_disjoint_buffer b1 b2
  end
  else
    loc_disjoint_buffer b1 b2
	 
let is_null #_ #_ #_ b = Null? b

let msub #a #rrel #rel b i len sub_rel =
  match b with
  | Null -> Null
  | Buffer max_len content i0 len0 () ->
    lemma_seq_sub_compatibility_is_transitive (U32.v max_len) rrel (U32.v i0) (U32.v i0 + U32.v len0) rel
                                              (U32.v i) (U32.v i + U32.v len) sub_rel;
    Buffer max_len content (U32.add i0 i) len ()

let moffset #a #rrel #rel b i sub_rel =
  match b with
  | Null -> Null
  | Buffer max_len content i0 len () ->
    lemma_seq_sub_compatibility_is_transitive (U32.v max_len) rrel (U32.v i0) (U32.v i0 + U32.v len) rel
                                              (U32.v i) (U32.v i + U32.v (U32.sub len i)) sub_rel;
    Buffer max_len content (U32.add i0 i) (U32.sub len i) ()

let index #_ #_ #_ b i =
  let open HST in
  let s = ! (Buffer?.content b) in
  Seq.index s (U32.v (Buffer?.idx b) + U32.v i)
let g_upd_seq #_ #_ #_ b s h =
  if Seq.length s = 0 then h
  else
    let s0 = HS.sel h (Buffer?.content b) in
    HS.upd h (Buffer?.content b) (replace_subseq s0 (U32.v (Buffer?.idx b)) (length b) s)

#push-options "--z3rlimit 32"
let g_upd_seq_as_seq #_ #_ #_ b s h =
  let h' = g_upd_seq b s h in
  if g_is_null b then assert (Seq.equal s Seq.empty)
  else begin
    assert (Seq.equal (as_seq h' b) s);
    // prove modifies_1_preserves_ubuffers
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    Seq.lemma_equal_instances_implies_equal_types ();
    modifies_1_modifies b h h'
  end
#pop-options

let upd' #_ #_ #_ b i v =
  let open HST in
  let Buffer max_length content idx len () = b in
  let s0 = !content in
  let sb0 = Seq.slice s0 (U32.v idx) (U32.v idx + U32.v len) in
  Buffer?.content b := replace_subseq s0 (U32.v idx) (U32.v len) (Seq.upd sb0 (U32.v i) v)

let recallable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot Type0 =
  (not (g_is_null b)) ==> (
    HST.is_eternal_region (frameOf b) /\
    not (HS.is_mm (Buffer?.content b)))

let recallable_null #_ #_ #_ = ()

let recallable_includes #_ #_ #_ #_ #_ #_ larger smaller =
  if Null? larger || Null? smaller then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)

let recall #_ #_ #_ b = if Null? b then () else HST.recall (Buffer?.content b)

let freeable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) =
  (not (g_is_null b)) /\
  HS.is_mm (Buffer?.content b) /\
  HST.is_eternal_region (frameOf b) /\
  U32.v (Buffer?.max_length b) > 0 /\
  Buffer?.idx b == 0ul /\
  Buffer?.length b == Buffer?.max_length b

let free #_ #_ #_ b = HST.rfree (Buffer?.content b)

let freeable_length #_ #_ #_ b = ()

let freeable_disjoint #_ #_ #_ #_ #_ #_ b1 b2 =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2 then
    MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)

let alloc_common (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U32.t) (mm:bool)
  :HST.ST (mbuffer a rrel rrel)
          (requires (fun h0 -> HST.is_eternal_region r /\ U32.v len > 0))
          (ensures (fun h0 b h1 -> alloc_post_common r (U32.v len) b h0 h1 /\
                                 as_seq h1 b == Seq.create (U32.v len) init /\
                                 HS.is_mm (Buffer?.content b) == mm /\
                                 Buffer?.idx b == 0ul /\
                                 Buffer?.length b == Buffer?.max_length b))
  = let s = Seq.create (U32.v len) init in
    lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
    let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
      if mm then HST.ralloc_mm r s else HST.ralloc r s
    in
    let b = Buffer len content 0ul len () in
    b

let mgcmalloc #_ #_ r init len = alloc_common r init len false

let mmalloc #_ #_ r init len = alloc_common r init len true

let malloca #a #rrel init len =
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.salloc (Seq.create (U32.v len) init)
  in
  let b = Buffer len content 0ul len () in
  b

let malloca_of_list #a #rrel init =
  let len = U32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.seq_of_list init in
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.salloc s
  in
  let b = Buffer len content 0ul len () in
  b

let mgcmalloc_of_list #a #rrel r init =
  let len = U32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.seq_of_list init in
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.ralloc r s
  in
  let b = Buffer len content 0ul len () in
  b

#push-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"
let blit #a #rrel1 #rrel2 #rel1 #rel2 src idx_src dst idx_dst len =
  let open HST in
  if len = 0ul then ()
  else
    let h = get () in
    let Buffer _ content1 idx1 length1 () = src in
    let Buffer _ content2 idx2 length2 () = dst in
    let s_full1 = !content1 in
    let s_full2 = !content2 in
    let s1 = Seq.slice s_full1 (U32.v idx1) (U32.v idx1 + U32.v length1) in
    let s2 = Seq.slice s_full2 (U32.v idx2) (U32.v idx2 + U32.v length2) in
    let s_sub_src = Seq.slice s1 (U32.v idx_src) (U32.v idx_src + U32.v len) in
    let s2' = replace_subseq s2 (U32.v idx_dst) (U32.v len) s_sub_src in
    let s_full2' = replace_subseq s_full2 (U32.v idx2) (U32.v length2) s2' in
    content2 := s_full2';
    g_upd_seq_as_seq dst s2' h  //for modifies clause
#pop-options

module MG = FStar.ModifiesGen

let abuffer' = ubuffer'

let coerce (t2: Type) (#t1: Type) (x1: t1) : Pure t2 (requires (t1 == t2)) (ensures (fun y -> y == x1)) = x1

let cloc_cls =
  assert_norm (MG.cls abuffer == MG.cls ubuffer);
  coerce (MG.cls abuffer) cls

let cloc_of_loc l =
  assert_norm (MG.cls abuffer == MG.cls ubuffer);
  coerce (MG.loc cloc_cls) l

let loc_of_cloc l =
  assert_norm (MG.cls abuffer == MG.cls ubuffer);
  coerce loc l

let loc_of_cloc_of_loc l = ()

let cloc_of_loc_of_cloc l = ()

let cloc_of_loc_none _ = ()

let cloc_of_loc_union _ _ = ()

let cloc_of_loc_addresses _ _ _ = ()

let cloc_of_loc_regions _ _ = ()

let loc_includes_to_cloc l1 l2 = ()

let loc_disjoint_to_cloc l1 l2 = ()

let modifies_to_cloc l h1 h2 = ()
