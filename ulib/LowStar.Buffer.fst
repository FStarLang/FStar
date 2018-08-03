module LowStar.Buffer

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module G = FStar.Ghost
module Seq = FStar.Seq

type vec (a: Type0) : nat -> Type0 =
  | VNil : vec a 0
  | VCons : (#n: nat { n > 0 } ) -> (vec_hd: a) -> (vec_tl: vec a (n - 1)) -> vec a n

noeq
type buffer' (a: Type0) : Type0 =
| Null
| Buffer:
  (max_length: U32.t { U32.v max_length > 0 } ) ->
  (content: HST.reference (vec a (U32.v max_length))) ->
  (idx: U32.t) ->
  (length: U32.t { U32.v idx + U32.v length <= U32.v max_length } ) ->
  buffer' a

let buffer = buffer'

(* Null pointer *)

let g_is_null #a b = Null? b

let null #a = Null

let null_unique #a b = ()

(* Memory safety *)

let unused_in #a b h =
  match b with
  | Null -> False
  | Buffer _ content _ _ -> content `HS.unused_in` h

let live #a h b =
  match b with
  | Null -> True
  | Buffer _ content _ _ -> h `HS.contains` content

let live_null a h = ()

let live_not_unused_in #a h b = ()

(* Regions and addresses, for allocation purposes *)

let frameOf #a b = if g_is_null b then HS.root else HS.frameOf (Buffer?.content b)

let as_addr #a b = if g_is_null b then 0 else HS.as_addr (Buffer?.content b)

let unused_in_equiv #a b h =
  if g_is_null b then Heap.not_addr_unused_in_nullptr (Map.sel (HS.get_hmap h) HS.root) else ()

let live_region_frameOf #a h b = ()

(* Contents *)

let len #a b =
  match b with
  | Null -> 0ul
  | Buffer _ _ _ len -> len

let len_null a = ()

let lseq = Seq.lseq

let rec lseq_of_vec (#a: Type0) (#n: nat) (l: vec a n) : Tot (lseq a n) =
  if n = 0
  then Seq.empty
  else Seq.cons (VCons?.vec_hd l) (lseq_of_vec (VCons?.vec_tl l))

let rec vec_of_lseq (#a: Type0) (#n: nat) (l: lseq a n) : Tot (vec a n) =
  if n = 0
  then VNil
  else VCons (Seq.head l) (vec_of_lseq (Seq.tail l))

val lseq_of_vec_of_lseq (#a: Type0) (#n: nat) (l: lseq a n) : Lemma
  (requires True)
  (ensures (Seq.equal (lseq_of_vec (vec_of_lseq l)) l))
  [SMTPat (lseq_of_vec (vec_of_lseq l))]

let rec lseq_of_vec_of_lseq #a #n l =
  if n = 0
  then ()
  else begin
    lseq_of_vec_of_lseq #_ #(n - 1) (Seq.tail l);
    Seq.cons_head_tail (lseq_of_vec (vec_of_lseq l));
    Seq.cons_head_tail l
  end

val vec_of_lseq_of_vec (#a: Type0) (#n: nat) (l: vec a n) : Lemma
  (requires True)
  (ensures (vec_of_lseq (lseq_of_vec l) == l))
  [SMTPat (vec_of_lseq (lseq_of_vec l))]

let rec vec_of_lseq_of_vec #a #n l =
  if n = 0
  then ()
  else begin
    Seq.cons_head_tail (lseq_of_vec l);
    vec_of_lseq_of_vec #_ #(n - 1) (VCons?.vec_tl l);
    Seq.lemma_tl (VCons?.vec_hd l) (lseq_of_vec (VCons?.vec_tl l))
  end

let as_seq #a h b =
  match b with
  | Null -> Seq.empty
  | Buffer max_len content idx len ->
    Seq.slice (lseq_of_vec (HS.sel h content)) (U32.v idx) (U32.v idx + U32.v len)

let length_as_seq #a h b = ()

(* Sub-buffers *)

let gsub #a b i len =
  match b with
  | Null -> Null
  | Buffer max_len content idx _ ->
    Buffer max_len content (U32.add idx i) len

let live_gsub #a h b i len = ()

let gsub_is_null #a b i len = ()

let len_gsub #a b i len' = ()

let frameOf_gsub #a b i len = ()

let as_addr_gsub #a b i len = ()

let gsub_inj #t b1 b2 i1 i2 len1 len2 = ()

let gsub_gsub #a b i1 len1 i2 len2 = ()

let gsub_zero_length #a b = ()

let as_seq_gsub #a h b i len =
  match b with
  | Null -> ()
  | Buffer _ content idx len0 ->
    Seq.slice_slice (lseq_of_vec (HS.sel h content)) (U32.v idx) (U32.v idx + U32.v len0) (U32.v i) (U32.v i + U32.v len)

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

let ubuffer_of_buffer' (#a: Type) (b: buffer a) : Tot (ubuffer (frameOf b) (as_addr b)) =
  if Null? b
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
= forall (t' : Type0) (b' : buffer t' ) .
  (frameOf b' == r /\ as_addr b' == a /\ ubuffer_of_buffer' b' == b /\ live h b') ==>
  (live h' b' /\ Seq.equal (as_seq h' b') (as_seq h b'))

val ubuffer_preserved (#r: HS.rid) (#a: nat) (b: ubuffer r a) (h h' : HS.mem) : GTot Type0

let ubuffer_preserved = ubuffer_preserved'

let ubuffer_preserved_intro
  (#r: HS.rid)
  (#a: nat)
  (b: ubuffer r a)
  (h h' : HS.mem)
  (f: (
    (t' : Type0) ->
    (b' : buffer t') ->
    Lemma
    (requires (frameOf b' == r /\ as_addr b' == a /\ ubuffer_of_buffer' b' == b /\ live h b'))
    (ensures (live h' b' /\ as_seq h' b' == as_seq h b'))
  ))
: Lemma
  (ubuffer_preserved b h h')
= let g'
    (t' : Type0)
    (b' : buffer t')
  : Lemma
    ((
      frameOf b' == r /\ as_addr b' == a /\ ubuffer_of_buffer' b' == b /\ live h b'
    ) ==> (
      live h' b' /\ as_seq h' b' == as_seq h b'
    ))
  = Classical.move_requires (f t') b'
  in
  Classical.forall_intro_2 g'

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
  ubuffer_preserved_intro b h1 h2 (fun t' b' ->
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

val ubuffer_of_buffer (#t: Type) (b: buffer t) : Tot (ubuffer (frameOf b) (as_addr b))

let ubuffer_of_buffer #t b = ubuffer_of_buffer' b

val ubuffer_preserved_elim (#t: Type) (b: buffer t) (h h' : HS.mem) : Lemma
  (requires (ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h' /\ live h b))
  (ensures (live h' b /\ as_seq h b == as_seq h' b))

let ubuffer_preserved_elim #t b h h' = ()

let unused_in_ubuffer_preserved
  (#t: Type)
  (b: buffer t)
  (h h' : HS.mem)
: Lemma
  (requires (b `unused_in` h))
  (ensures (ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h'))
= Classical.move_requires (fun b -> live_not_unused_in #t h b) b;
  live_null t h;
  null_unique b;
  unused_in_equiv b h;
  addr_unused_in_ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h'

let ubuffer_includes' (larger smaller: ubuffer_) : GTot Type0 =
  larger.b_is_mm == smaller.b_is_mm /\
  larger.b_max_length == smaller.b_max_length /\
  larger.b_offset <= smaller.b_offset /\
  smaller.b_offset + smaller.b_length <= larger.b_offset + larger.b_length

val ubuffer_includes (#r: HS.rid) (#a: nat) (larger smaller: ubuffer r a) : GTot Type0

let ubuffer_includes #r #a larger smaller =
  ubuffer_includes' (G.reveal larger) (G.reveal smaller)

val ubuffer_includes_refl (#r: HS.rid) (#a: nat) (b: ubuffer r a) : Lemma
  (b `ubuffer_includes` b)

let ubuffer_includes_refl #r #a b = ()

val ubuffer_includes_trans (#r: HS.rid) (#a: nat) (b1 b2 b3: ubuffer r a) : Lemma
  (requires (b1 `ubuffer_includes` b2 /\ b2 `ubuffer_includes` b3))
  (ensures (b1 `ubuffer_includes` b3))

let ubuffer_includes_trans #r #a b1 b2 b3 = ()

val ubuffer_includes_ubuffer_preserved (#r: HS.rid) (#a: nat) (larger smaller: ubuffer r a) (h1 h2: HS.mem) : Lemma
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
  )

let ubuffer_disjoint' (x1 x2: ubuffer_) : GTot Type0 =
  (x1.b_max_length == x2.b_max_length /\
    (x1.b_offset + x1.b_length <= x2.b_offset \/
     x2.b_offset + x2.b_length <= x1.b_offset))

val ubuffer_disjoint (#r: HS.rid) (#a: nat) (b1 b2: ubuffer r a) : GTot Type0

let ubuffer_disjoint #r #a b1 b2 =
  ubuffer_disjoint' (G.reveal b1) (G.reveal b2)

val ubuffer_disjoint_sym (#r: HS.rid) (#a: nat) (b1 b2: ubuffer r a) : Lemma
  (ubuffer_disjoint b1 b2 <==> ubuffer_disjoint b2 b1)

let ubuffer_disjoint_sym #r #a b1 b2 = ()

val ubuffer_disjoint_includes (#r: HS.rid) (#a: nat) (larger1 larger2: ubuffer r a) (smaller1 smaller2: ubuffer r a) : Lemma
  (requires (ubuffer_disjoint larger1 larger2 /\ larger1 `ubuffer_includes` smaller1 /\ larger2 `ubuffer_includes` smaller2))
  (ensures (ubuffer_disjoint smaller1 smaller2))

let ubuffer_disjoint_includes #r #a larger1 larger2 smaller1 smaller2 = ()

val liveness_preservation_intro
  (#t: Type) (h h' : HS.mem) (b: buffer t)
  (f: (
    (t' : Type) ->
    (pre: Preorder.preorder t') ->
    (r: HS.mreference t' pre) ->
    Lemma
    (requires (HS.frameOf r == frameOf b /\ HS.as_addr r == as_addr b /\ h `HS.contains` r))
    (ensures (h' `HS.contains` r))
  ))
: Lemma
  (requires (live h b))
  (ensures (live h' b))

let liveness_preservation_intro #t h h' b f =
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

let modifies_1_preserves_mreferences
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0
= forall (a' : Type) (pre: Preorder.preorder a') (r' : HS.mreference  a' pre) .
  ((frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r') ==>
  (h2 `HS.contains` r' /\ HS.sel h1 r' == HS.sel h2 r')

let modifies_1_preserves_ubuffers
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0
= forall (b' : ubuffer (frameOf b) (as_addr b)) .
  (ubuffer_disjoint #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) b') ==> ubuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2

let modifies_1_preserves_livenesses
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0
= forall (a' : Type) (pre: Preorder.preorder a') (r' : HS.mreference  a' pre) .
  h1 `HS.contains` r' ==>
  h2 `HS.contains` r'

let modifies_1' 
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0
= modifies_0_preserves_regions h1 h2 /\
  modifies_1_preserves_mreferences b h1 h2 /\
  modifies_1_preserves_livenesses b h1 h2 /\
  modifies_0_preserves_not_unused_in h1 h2 /\
  modifies_1_preserves_ubuffers b h1 h2

val modifies_1 (#a: Type) (b: buffer a) (h1 h2: HS.mem) : GTot Type0

let modifies_1 = modifies_1'

val modifies_1_live_region (#a: Type) (b: buffer a) (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_1 b h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

let modifies_1_live_region #a b h1 h2 r = ()

val modifies_1_liveness
  (#a: Type) (b: buffer a) (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_1 b h1 h2 /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r'))

let modifies_1_liveness #a b h1 h2 #a' #pre r' = ()

val modifies_1_unused_in
  (#t: Type)
  (b: buffer t)
  (h1 h2: HS.mem)
  (r: HS.rid)
  (n: nat)
: Lemma
  (requires (
    modifies_1 b h1 h2 /\
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)
  ))
  (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))

let modifies_1_unused_in #t b h1 h2 r n = ()

val modifies_1_mreference
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_1 b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))

let modifies_1_mreference #a b h1 h2 #a' #pre r' = ()

val modifies_1_ubuffer
  (#a: Type) (b : buffer a)
  (h1 h2: HS.mem)
  (b' : ubuffer (frameOf b) (as_addr b))
: Lemma
  (requires (modifies_1 b h1 h2 /\ ubuffer_disjoint #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) b'))
  (ensures (ubuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2))

let modifies_1_ubuffer #a b h1 h2 b' = ()

val modifies_1_null
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_1 b h1 h2 /\ g_is_null b))
  (ensures (modifies_0 h1 h2))

let modifies_1_null #a b h1 h2 = ()

let modifies_addr_of_preserves_not_unused_in (#t:Type) (b: buffer t) (h1 h2: HS.mem) : GTot Type0 =
  forall (r: HS.rid) (n: nat) . (
    (r <> frameOf b \/ n <> as_addr b) /\
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)  
  ) ==> (
    n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)
  )

let modifies_addr_of'
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0
= modifies_0_preserves_regions h1 h2 /\
  modifies_1_preserves_mreferences b h1 h2 /\
  modifies_addr_of_preserves_not_unused_in b h1 h2

val modifies_addr_of
  (#a: Type)
  (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0

let modifies_addr_of = modifies_addr_of'

val modifies_addr_of_live_region (#a: Type) (b: buffer a) (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_addr_of b h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

let modifies_addr_of_live_region #a b h1 h2 r = ()

val modifies_addr_of_mreference
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_addr_of b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))

let modifies_addr_of_mreference #a b h1 h2 #a' #pre r' = ()

val modifies_addr_of_unused_in
  (#t: Type)
  (b: buffer t)
  (h1 h2: HS.mem)
  (r: HS.rid)
  (n: nat)
: Lemma
  (requires (
    modifies_addr_of b h1 h2 /\
    (r <> frameOf b \/ n <> as_addr b) /\
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)
  ))
  (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))

let modifies_addr_of_unused_in #t b h1 h2 r n = ()

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

let loc_buffer #t b =
  if g_is_null b
  then
    MG.loc_none
  else
    MG.loc_of_aloc #_ #_ #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let loc_buffer_null t = ()

let loc_addresses = MG.loc_addresses

let loc_regions = MG.loc_regions

let loc_includes = MG.loc_includes

let loc_includes_refl = MG.loc_includes_refl

let loc_includes_trans = MG.loc_includes_trans

let loc_includes_union_r = MG.loc_includes_union_r

let loc_includes_union_l = MG.loc_includes_union_l

let loc_includes_none = MG.loc_includes_none

val loc_includes_buffer
  (#t: Type)
  (b1 b2: buffer t)
: Lemma
  (requires (frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2 /\ ubuffer_includes #(frameOf b1) #(as_addr b1) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)))
  (ensures (loc_includes (loc_buffer b1) (loc_buffer b2)))

let loc_includes_buffer #t b1 b2 =
  assert (frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2);
  let t1 = ubuffer (frameOf b1) (as_addr b1) in
  let t2 = ubuffer (frameOf b2) (as_addr b2) in
  assert (t1 == t2);
  MG.loc_includes_aloc #_ #cls #(frameOf b1) #(as_addr b1) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2 <: t1)

let loc_includes_gsub_buffer_r l #t b i len =
  let b' = gsub b i len in
  loc_includes_buffer b b';
  loc_includes_trans l (loc_buffer b) (loc_buffer b')

let loc_includes_gsub_buffer_l #t b i1 len1 i2 len2 =
  let b1 = gsub b i1 len1 in
  let b2 = gsub b1 (U32.sub i2 i1) len2 in
  loc_includes_buffer b1 b2

let loc_includes_as_seq #a h1 h2 larger smaller =
  if Null? smaller then () else
  if Null? larger then begin
    MG.loc_includes_none_elim (loc_buffer smaller);
    MG.loc_of_aloc_not_none #_ #cls #(frameOf smaller) #(as_addr smaller) (ubuffer_of_buffer smaller)
  end else begin
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller);
    let ul = Ghost.reveal (ubuffer_of_buffer larger) in
    let us = Ghost.reveal (ubuffer_of_buffer smaller) in
    assert (as_seq h1 smaller == Seq.slice (as_seq h1 larger) (us.b_offset - ul.b_offset) (us.b_offset - ul.b_offset + length smaller));
    assert (as_seq h2 smaller == Seq.slice (as_seq h2 larger) (us.b_offset - ul.b_offset) (us.b_offset - ul.b_offset + length smaller))
  end

let loc_includes_addresses_buffer #t preserve_liveness r s p =
  MG.loc_includes_addresses_aloc #_ #cls preserve_liveness r s #(as_addr p) (ubuffer_of_buffer p)

let loc_includes_region_buffer #t preserve_liveness s b =
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

val loc_disjoint_buffer
  (#t1 #t2: Type)
  (b1: buffer t1)
  (b2: buffer t2)
: Lemma
  (requires ((frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2) ==> ubuffer_disjoint #(frameOf b1) #(as_addr b1) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)))
  (ensures (loc_disjoint (loc_buffer b1) (loc_buffer b2)))

let loc_disjoint_buffer #t1 #t2 b1 b2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)

let loc_disjoint_gsub_buffer #t b i1 len1 i2 len2 =
  loc_disjoint_buffer (gsub b i1 len1) (gsub b i2 len2)

let loc_disjoint_addresses = MG.loc_disjoint_addresses_intro #_ #cls

let loc_disjoint_regions = MG.loc_disjoint_regions #_ #cls

let modifies = MG.modifies

let modifies_live_region = MG.modifies_live_region

let modifies_mreference_elim = MG.modifies_mreference_elim

let modifies_buffer_elim #t1 b p h h' =
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

let address_liveness_insensitive_buffer #t b =
  MG.loc_includes_address_liveness_insensitive_locs_aloc #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let address_liveness_insensitive_addresses =
  MG.loc_includes_address_liveness_insensitive_locs_addresses cls

let region_liveness_insensitive_buffer #t b =
  MG.loc_includes_region_liveness_insensitive_locs_loc_of_aloc #_ cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let region_liveness_insensitive_addresses =
  MG.loc_includes_region_liveness_insensitive_locs_loc_addresses cls

let region_liveness_insensitive_regions =
  MG.loc_includes_region_liveness_insensitive_locs_loc_regions cls

let region_liveness_insensitive_address_liveness_insensitive =
  MG.loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs cls

let modifies_liveness_insensitive_mreference = MG.modifies_preserves_liveness

let modifies_liveness_insensitive_buffer l1 l2 h h' #t x =
  if g_is_null x
  then ()
  else
    liveness_preservation_intro h h' x (fun t' pre r ->
      MG.modifies_preserves_liveness_strong l1 l2 h h' r (ubuffer_of_buffer x)
    )

let modifies_liveness_insensitive_region = MG.modifies_preserves_region_liveness

let modifies_liveness_insensitive_region_mreference = MG.modifies_preserves_region_liveness_reference

let modifies_liveness_insensitive_region_buffer l1 l2 h h' #t x =
  if g_is_null x
  then ()
  else
    MG.modifies_preserves_region_liveness_aloc l1 l2 h h' #(frameOf x) #(as_addr x) (ubuffer_of_buffer x)

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
  (#t: Type)
  (b: buffer t)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_1 b h1 h2))
  (ensures (modifies (loc_buffer b) h1 h2))

let modifies_1_modifies #t b h1 h2 =
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
  (#t: Type)
  (b: buffer t)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_addr_of b h1 h2))
  (ensures (modifies (loc_addr_of_buffer b) h1 h2))

let modifies_addr_of_modifies #t b h1 h2 =
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

let live_loc_not_unused_in #t b h =
  unused_in_equiv b h;
  Classical.move_requires (MG.does_not_contain_addr_addr_unused_in h) (frameOf b, as_addr b);
  MG.loc_addresses_not_unused_in cls (frameOf b) (Set.singleton (as_addr b)) h;
  ()

let unused_in_loc_unused_in #t b h =
  unused_in_equiv b h;
  Classical.move_requires (MG.addr_unused_in_does_not_contain_addr h) (frameOf b, as_addr b);
  MG.loc_addresses_unused_in cls (frameOf b) (Set.singleton (as_addr b)) h;
  ()

let modifies_address_liveness_insensitive_unused_in =
  MG.modifies_address_liveness_insensitive_unused_in cls

let mreference_live_loc_not_unused_in =
  MG.mreference_live_loc_not_unused_in cls

let mreference_unused_in_loc_unused_in =
  MG.mreference_unused_in_loc_unused_in cls

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

let new_region_modifies_inert = new_region_modifies

let popped_modifies_inert = popped_modifies

let modifies_inert_loc_unused_in l h1 h2 l' =
  modifies_loc_includes address_liveness_insensitive_locs h1 h2 l;
  modifies_address_liveness_insensitive_unused_in h1 h2;
  loc_includes_trans (loc_unused_in h1) (loc_unused_in h2) l'


let disjoint_neq #a1 #a2 b1 b2 =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2
  then
    MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)
  else ()

let includes_live #a h larger smaller =
  if Null? larger || Null? smaller
  then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)

let includes_frameOf_as_addr #a larger smaller =
  if Null? larger || Null? smaller
  then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)

let pointer_distinct_sel_disjoint #a b1 b2 h =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2
  then begin
    let t1 = vec a (U32.v (Buffer?.max_length b1)) in
    let t2 = vec a (U32.v (Buffer?.max_length b2)) in
    let r1 : HST.reference t1 = Buffer?.content b1 in
    let r2' : HST.reference t2 = Buffer?.content b2 in
    assert (Buffer?.max_length b1 == Buffer?.max_length b2);
    assert (t1 == t2);
    let r2 : HS.reference t1 = r2' in
    HS.reference_distinct_sel_disjoint h (Buffer?.content b1) r2;
    loc_disjoint_buffer b1 b2
  end
  else
    loc_disjoint_buffer b1 b2
            

(* Basic stateful operations *)

let is_null #a b = Null? b

let sub #a b i len =
  match b with
  | Null -> Null
  | Buffer max_len content i0 len0 ->
    Buffer max_len content (U32.add i0 i) len

let offset #a b i =
  match b with
  | Null -> Null
  | Buffer max_len content i0 len ->
    Buffer max_len content (U32.add i0 i) (U32.sub len i) 

let index #a b i =
  let open HST in
  let s = ! (Buffer?.content b) in
  Seq.index (lseq_of_vec s) (U32.v (Buffer?.idx b) + U32.v i)

(* Update *)

let g_upd' (#a:Type)
              (b:buffer a)
              (i:nat{i < length b})
              (v:a)
              (h:HS.mem{live h b})
  : GTot HS.mem
  = let n = length b in
    if n = 0 then h
    else
      let s0 = lseq_of_vec (HS.sel h (Buffer?.content b)) in
      let v = vec_of_lseq (Seq.upd s0 (U32.v (Buffer?.idx b) + i) v) in
      HS.upd h (Buffer?.content b) v

#set-options "--z3rlimit 32"

let g_upd'_as_seq (#a:Type)
                     (b:buffer a)
                     (i:nat{i < length b})
                     (v:a)
                     (h:HS.mem{live h b})
  : Lemma (let h' = g_upd' b i v h in
           modifies (loc_buffer b) h h' /\
           live h' b /\
           as_seq h' b == Seq.upd (as_seq h b) i v)
= let h' = g_upd' b i v h in
  assert (as_seq h' b `Seq.equal` Seq.upd (as_seq h b) i v);
  // prove modifies_1_preserves_ubuffers
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  modifies_1_modifies b h h'

#reset-options

let rec g_upd_seq' (#a:Type)
              (b:buffer a)
              (s:Seq.lseq a (length b))
              (h:HS.mem{live h b})
  : GTot HS.mem
    (decreases (Seq.length s))
  = if Seq.length s = 0 then h else
      let h1 = g_upd' b 0 (Seq.head s) h in
      g_upd_seq' (gsub b 1ul (len b `U32.sub` 1ul)) (Seq.slice s 1 (Seq.length s)) h1

let g_upd_seq = g_upd_seq'

#set-options "--z3rlimit 16"

let rec g_upd_seq_as_seq' (#a:Type)
                     (b:buffer a)
                     (s:Seq.lseq a (length b))
                     (h:HS.mem{live h b})
  : Lemma (requires True) (ensures (let h' = g_upd_seq' b s h in
           modifies (loc_buffer b) h h' /\
           live h' b /\
           as_seq h' b == s))
    (decreases (Seq.length s))
= let h'= g_upd_seq' b s h in
  if Seq.length s = 0 then assert (as_seq h' b `Seq.equal` s) else begin
    let h1 = g_upd' b 0 (Seq.head s) h in
    g_upd'_as_seq b 0 (Seq.head s) h;
    g_upd_seq_as_seq' (gsub b 1ul (len b `U32.sub` 1ul)) (Seq.slice s 1 (Seq.length s)) h1;
    assert (Seq.head (as_seq h' b) == Seq.head (as_seq h' (gsub b 0ul 1ul)));
    assert (as_seq h' (gsub b 0ul 1ul) == as_seq h1 (gsub b 0ul 1ul));
    assert (Seq.head (as_seq h1 (gsub b 0ul 1ul)) == Seq.head (as_seq h1 (gsub b 0ul 1ul)));
    assert (Seq.head (as_seq h' b) == Seq.head s);
    assert (Seq.tail (as_seq h' b) == Seq.tail s);
    Seq.cons_head_tail (as_seq h' b);
    Seq.cons_head_tail s
  end

let g_upd_seq_as_seq = g_upd_seq_as_seq'

let upd #a b i v =
  let open HST in
  let h0 = get () in
  let s0 = lseq_of_vec ! (Buffer?.content b) in
  let s = Seq.upd s0 (U32.v (Buffer?.idx b) + U32.v i) v in
  Buffer?.content b := vec_of_lseq s;
  // prove modifies_1_preserves_ubuffers
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  let h = HST.get () in
  modifies_1_modifies b h0 h

#reset-options

(* Recall *)

let recallable' (#a: Type) (b: buffer a) : GTot Type0 =
  (not (g_is_null b)) ==> (
    HST.is_eternal_region (frameOf b) /\
    not (HS.is_mm (Buffer?.content b))
  )

let recallable = recallable'

let recallable_includes #a larger smaller =
  if Null? larger || Null? smaller
  then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)

let recall #a b =
  if Null? b
  then ()
  else
    HST.recall (Buffer?.content b)

(* Deallocation *)

let freeable' (#a: Type) (b: buffer a) : GTot Type0 =
  (not (g_is_null b)) /\
  HS.is_mm (Buffer?.content b) /\
  HST.is_eternal_region (frameOf b) /\
  Buffer?.idx b == 0ul /\
  Buffer?.length b == Buffer?.max_length b

let freeable = freeable'

let free #a b =
  HST.rfree (Buffer?.content b)

let freeable_length #a b = ()

let freeable_disjoint #a1 #a2 b1 b2 =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2
  then
    MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)
  else ()


(* Allocation *)

let alloc_common
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: U32.t)
  (mm: bool)
: HST.ST (buffer a)
  (requires (fun h0 -> HST.is_eternal_region r /\ U32.v len > 0))
  (ensures (fun h0 b h1 ->
    alloc_post_common r (U32.v len) b h0 h1 /\
    as_seq h1 b == Seq.create (U32.v len) init /\
    HS.is_mm (Buffer?.content b) == mm /\
    Buffer?.idx b == 0ul /\
    Buffer?.length b == Buffer?.max_length b
  ))
= let s = vec_of_lseq (Seq.create (U32.v len) init) in
  let content: HST.reference (vec a (U32.v len)) =
    if mm then HST.ralloc_mm r s else HST.ralloc r s
  in
  let b = Buffer len content 0ul len in
  b

let gcmalloc #a r init len =
  alloc_common r init len false

let malloc #a r init len =
  alloc_common r init len true

let alloca #a init len =
  let content: HST.reference (vec a (U32.v len)) =
    HST.salloc (vec_of_lseq (Seq.create (U32.v len) init))
  in
  let b = Buffer len content 0ul len in
  b

let alloca_of_list #a init =
  let len = U32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.seq_of_list init in
  let content: HST.reference (vec a (U32.v len)) =
    HST.salloc (vec_of_lseq s)
  in
  let b = Buffer len content 0ul len in
  b

let gcmalloc_of_list #a r init =
  let len = U32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.seq_of_list init in
  let content: HST.reference (vec a (U32.v len)) =
    HST.ralloc r (vec_of_lseq s)
  in
  let b = Buffer len content 0ul len in
  b

let rec blit #t src idx_src dst idx_dst len
= let h0 = HST.get () in
  if len = 0ul then ()
  else begin
    let len' = U32.(len -^ 1ul) in
    blit #t src idx_src dst idx_dst len';
    let z = U32.(index src (idx_src +^ len')) in
    upd dst (U32.(idx_dst +^ len')) z;
    let h1 = HST.get() in
    Seq.snoc_slice_index (as_seq h1 dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len');
    Seq.cons_head_tail (Seq.slice (as_seq h0 dst) (U32.v idx_dst + U32.v len') (length dst));
    Seq.cons_head_tail (Seq.slice (as_seq h1 dst) (U32.v idx_dst + U32.v len') (length dst))
  end



(* type class *)

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
