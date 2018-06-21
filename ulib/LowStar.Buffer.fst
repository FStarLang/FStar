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
  then Seq.createEmpty
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
  | Null -> Seq.createEmpty
  | Buffer max_len content idx len ->
    Seq.slice (lseq_of_vec (HS.sel h content)) (U32.v idx) (U32.v idx + U32.v len)

let length_as_seq #a h b = ()

(* Inclusion *)

let includes #a larger smaller =
  match larger, smaller with
  | Null, Null -> True
  | Buffer max_len_l content_l idx_l len_l, Buffer max_len_s content_s idx_s len_s ->
    max_len_l == max_len_s /\
    content_l == content_s /\
    U32.v idx_s >= U32.v idx_l /\
    U32.v idx_l + U32.v len_l >= U32.v idx_s + U32.v len_s
  | _ -> False

let includes_live #a h larger smaller = ()

let includes_as_seq #a h1 h2 larger smaller =
  match larger, smaller with
  | Buffer max_len_l content_l idx_l len_l, Buffer max_len_s content_s idx_s len_s ->
    Seq.slice_slice (lseq_of_vec (HS.sel h1 content_l)) (U32.v idx_l) (U32.v idx_l + U32.v len_l) (U32.v idx_s - U32.v idx_l) (U32.v idx_s - U32.v idx_l + U32.v len_s);
    Seq.slice_slice (lseq_of_vec (HS.sel h2 content_l)) (U32.v idx_l) (U32.v idx_l + U32.v len_l) (U32.v idx_s - U32.v idx_l) (U32.v idx_s - U32.v idx_l + U32.v len_s)
  | _ -> ()

let includes_refl #a x = ()

let includes_trans #a x y z = ()

let includes_frameOf_as_addr #a larger smaller = ()

(* Sub-buffers *)

let gsub #a b i len =
  match b with
  | Null -> Null
  | Buffer max_len content idx _ ->
    Buffer max_len content (U32.add idx i) len

let live_gsub #a h b i len = ()

let includes_gsub #a b i len = ()

let len_gsub #a b i len' = ()

let gsub_gsub #a b i1 len1 i2 len2 = ()

let gsub_zero_length #a b = ()

let as_seq_gsub #a h b i len =
  match b with
  | Null -> ()
  | Buffer _ content idx len0 ->
    Seq.slice_slice (lseq_of_vec (HS.sel h content)) (U32.v idx) (U32.v idx + U32.v len0) (U32.v i) (U32.v i + U32.v len)

(* Disjointness *)

let disjoint #a1 #a2 b1 b2 =
  match b1, b2 with
  | Buffer max_len1 content1 idx1 len1, Buffer max_len2 content2 idx2 len2 ->
    if HS.frameOf content1 = HS.frameOf content2 && HS.as_addr content1 = HS.as_addr content2
    then
      (max_len1 == max_len2 /\ (
        U32.v idx1 + U32.v len1 <= U32.v idx2 \/
        U32.v idx2 + U32.v len2 <= U32.v idx1
      ))
    else True
  | _ -> True

let disjoint_sym #a1 #a2 b1 b2 = ()

let disjoint_includes_l #a1 #a2 b1 b1' b2 = ()

let disjoint_includes_r #a1 #a2 b1 b2 b2' = ()

let live_unused_in_disjoint #a1 #a2 h b1 b2 = ()

let as_addr_disjoint #a1 #a2 b1 b2 = ()

let disjoint_null a1 #a2 b2 = ()

let gsub_disjoint #a b i1 len1 i2 len2 = ()

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
    HS.reference_distinct_sel_disjoint h (Buffer?.content b1) r2
  end
  else ()


(* Untyped view of buffers, used only to implement the generic modifies clause. DO NOT USE in client code. *)

noeq
type abuffer_
: Type0
= {
  b_max_length: nat;
  b_offset: nat;
  b_length: nat;
}

let abuffer' region addr = (x: abuffer_ { x.b_offset + x.b_length <= x.b_max_length } )

let abuffer_of_buffer' (#a: Type) (b: buffer a) : Tot (abuffer (frameOf b) (as_addr b)) =
  if Null? b
  then
    Ghost.hide ({
      b_max_length = 0;
      b_offset = 0;
      b_length = 0;
    })
  else
    Ghost.hide ({
      b_max_length = U32.v (Buffer?.max_length b);
      b_offset = U32.v (Buffer?.idx b);
      b_length = U32.v (Buffer?.length b);
    })

let abuffer_preserved' 
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h h' : HS.mem)
: GTot Type0
= forall (t' : Type0) (b' : buffer t' ) .
  (frameOf b' == r /\ as_addr b' == a /\ abuffer_of_buffer' b' == b /\ live h b') ==>
  (live h' b' /\ Seq.equal (as_seq h' b') (as_seq h b'))

let abuffer_preserved = abuffer_preserved'

let abuffer_preserved_intro
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h h' : HS.mem)
  (f: (
    (t' : Type0) ->
    (b' : buffer t') ->
    Lemma
    (requires (frameOf b' == r /\ as_addr b' == a /\ abuffer_of_buffer' b' == b /\ live h b'))
    (ensures (live h' b' /\ as_seq h' b' == as_seq h b'))
  ))
: Lemma
  (abuffer_preserved b h h')
= let g'
    (t' : Type0)
    (b' : buffer t')
  : Lemma
    ((
      frameOf b' == r /\ as_addr b' == a /\ abuffer_of_buffer' b' == b /\ live h b'
    ) ==> (
      live h' b' /\ as_seq h' b' == as_seq h b'
    ))
  = Classical.move_requires (f t') b'
  in
  Classical.forall_intro_2 g'

let abuffer_preserved_refl #r #a b h = ()

let abuffer_preserved_trans #r #a b h1 h2 h3 = ()

let same_mreference_abuffer_preserved #r #a b h1 h2 f =
  abuffer_preserved_intro b h1 h2 (fun t' b' ->
    if Null? b'
    then ()
    else
      f _ _ (Buffer?.content b')
  )

let addr_unused_in_abuffer_preserved #r #a b h1 h2 = ()

let abuffer_of_buffer #t b = abuffer_of_buffer' b

let abuffer_preserved_elim #t b h h' = ()

let abuffer_includes' (larger smaller: abuffer_) : GTot Type0 =
  larger.b_max_length == smaller.b_max_length /\
  larger.b_offset <= smaller.b_offset /\
  smaller.b_offset + smaller.b_length <= larger.b_offset + larger.b_length

let abuffer_includes #r #a larger smaller =
  abuffer_includes' (G.reveal larger) (G.reveal smaller)

let abuffer_includes_refl #r #a b = ()

let abuffer_includes_trans #r #a b1 b2 b3 = ()

let abuffer_includes_abuffer_preserved #r #a larger smaller h1 h2 =
  abuffer_preserved_intro smaller h1 h2 (fun t' b' ->
    if Null? b'
    then ()
    else
      let (Buffer max_len content idx' len') = b' in
      let idx = U32.uint_to_t (G.reveal larger).b_offset in
      let len = U32.uint_to_t (G.reveal larger).b_length in
      let larger' = Buffer max_len content idx len in
      assert (b' == gsub larger' (U32.sub idx' idx) len');
      abuffer_preserved_elim larger' h1 h2
  )

let abuffer_includes_intro #t larger smaller = ()

let abuffer_disjoint' (x1 x2: abuffer_) : GTot Type0 =
  (x1.b_max_length == x2.b_max_length /\
    (x1.b_offset + x1.b_length <= x2.b_offset \/
     x2.b_offset + x2.b_length <= x1.b_offset))

let abuffer_disjoint #r #a b1 b2 =
  abuffer_disjoint' (G.reveal b1) (G.reveal b2)

let abuffer_disjoint_sym #r #a b1 b2 = ()

let abuffer_disjoint_includes #r #a larger1 larger2 smaller1 smaller2 = ()

let abuffer_disjoint_intro #t1 #t2 b1 b2 = ()

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

let modifies_0 = modifies_0'

let modifies_0_live_region h1 h2 r = ()

let modifies_0_mreference #a #pre h1 h2 r = ()

let modifies_0_unused_in h1 h2 r n = ()

let modifies_1_preserves_mreferences
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0
= forall (a' : Type) (pre: Preorder.preorder a') (r' : HS.mreference  a' pre) .
  ((frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r') ==>
  (h2 `HS.contains` r' /\ HS.sel h1 r' == HS.sel h2 r')

let modifies_1_preserves_abuffers
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0
= forall (b' : abuffer (frameOf b) (as_addr b)) .
  (abuffer_disjoint #(frameOf b) #(as_addr b) (abuffer_of_buffer b) b') ==> abuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2

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
  modifies_1_preserves_abuffers b h1 h2

let modifies_1 = modifies_1'

let modifies_1_live_region #a b h1 h2 r = ()

let modifies_1_liveness #a b h1 h2 #a' #pre r' = ()

let modifies_1_unused_in #t b h1 h2 r n = ()

let modifies_1_mreference #a b h1 h2 #a' #pre r' = ()

let modifies_1_abuffer #a b h1 h2 b' = ()

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

let modifies_addr_of = modifies_addr_of'

let modifies_addr_of_live_region #a b h1 h2 r = ()

let modifies_addr_of_mreference #a b h1 h2 #a' #pre r' = ()

let modifies_addr_of_unused_in #t b h1 h2 r n = ()



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

let g_upd_seq #a b s h
  : GTot HS.mem
  = let n = length b in
    if n = 0 then h
    else
      let s0 = lseq_of_vec (HS.sel h (Buffer?.content b)) in
      let prefix, suffix = Seq.split s0 (U32.v (Buffer?.idx b)) in
      let _, tail = Seq.split suffix (length b) in
      let v = vec_of_lseq (prefix `Seq.append` s `Seq.append` tail) in
      HS.upd h (Buffer?.content b) v

#reset-options "--max_fuel 0 --max_ifuel 1"
let g_upd_seq_as_seq (#a:Type) (b:buffer a) (s:lseq a (length b)) (h:HS.mem{live h b})
  = let h' = g_upd_seq b s h in
    assert (as_seq (g_upd_seq b s h) b `Seq.equal` s);
    // prove modifies_1_preserves_abuffers
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ()
#reset-options

let upd #a b i v =
  let open HST in
  let h0 = get () in
  let s0 = lseq_of_vec ! (Buffer?.content b) in
  let s = Seq.upd s0 (U32.v (Buffer?.idx b) + U32.v i) v in
  Buffer?.content b := vec_of_lseq s;
  // prove modifies_1_preserves_abuffers
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ()

(* Recall *)

let recallable' (#a: Type) (b: buffer a) : GTot Type0 =
  (not (g_is_null b)) ==> (
    HST.is_eternal_region (frameOf b) /\
    not (HS.is_mm (Buffer?.content b))
  )

let recallable = recallable'

let recallable_includes #a larger smaller = ()

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
  let s = Seq.of_list init in
  Seq.lemma_of_list_length s init;
  let content: HST.reference (vec a (U32.v len)) =
    HST.salloc (vec_of_lseq s)
  in
  let b = Buffer len content 0ul len in
  b

let gcmalloc_of_list #a r init =
  let len = U32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.of_list init in
  Seq.lemma_of_list_length s init;
  let content: HST.reference (vec a (U32.v len)) =
    HST.ralloc r (vec_of_lseq s)
  in
  let b = Buffer len content 0ul len in
  b
