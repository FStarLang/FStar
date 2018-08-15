module LowStar.BufVector

open FStar.All
open FStar.Integers
open LowStar.Modifies
open LowStar.Vector

module HH = FStar.Monotonic.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module S = FStar.Seq
module B = LowStar.Buffer
module V = LowStar.Vector

module U32 = FStar.UInt32

type buf_vector a = V.vector (B.buffer a)

val new_region_:
  r0:HH.rid -> 
  HST.ST HH.rid
    (fun _ -> HST.is_eternal_region r0)
    (fun h0 r1 h1 ->
      MHS.fresh_region r1 h0 h1 /\
      HH.extends r1 r0 /\
      MHS.get_hmap h1 == Map.upd (MHS.get_hmap h0) r1 Monotonic.Heap.emp /\
      HH.color r1 = HH.color r0 /\
      HyperStack.ST.is_eternal_region r1 /\
      modifies loc_none h0 h1)
let new_region_ r0 =
  let hh0 = HST.get () in
  let r1 = HST.new_region r0 in
  let hh1 = HST.get () in
  B.modifies_none_modifies hh0 hh1;
  r1

type erid = rid:HH.rid{HST.is_eternal_region rid}

val root: erid
let root = HH.root

/// Lemmas for sequence

// val slice_index:
//   #a:Type -> s:S.seq a ->
//   i:nat -> j:nat{i <= j && j <= S.length s} ->
//   k:nat{k < j - i} ->
//   Lemma (S.index (S.slice s i j) k == S.index s (i + k))
// let slice_index #a s i j k = ()

/// The invariant

val buffer_inv_liveness:
  #a:Type0 -> blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> b:B.buffer a -> GTot Type0
let buffer_inv_liveness #a blen h b =
  B.live h b /\ B.len b = blen /\ B.freeable b

val buffers_inv_liveness:
  #a:Type0 -> blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> bv:buf_vector a -> 
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of bv} ->
  GTot Type0
let buffers_inv_liveness #a blen h bv i j =
  V.forall_ h bv i j (buffer_inv_liveness blen h)

val bv_inv_liveness:
  #a:Type0 -> blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> bv:buf_vector a -> GTot Type0
let bv_inv_liveness #a blen h bv =
  V.live h bv /\ V.freeable bv /\
  buffers_inv_liveness blen h bv 0ul (V.size_of bv)

val buffers_inv_region:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a -> 
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of bv} ->
  GTot Type0
let buffers_inv_region #a h bv i j =
  V.forall_ h bv i j
    (fun b -> HH.extends (B.frameOf b) (V.frameOf bv)) /\
  V.forall2 h bv i j
    (fun b1 b2 -> HH.disjoint (B.frameOf b1) (B.frameOf b2))

val bv_inv_region:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a -> GTot Type0
let bv_inv_region #a h bv =
  HST.is_eternal_region (V.frameOf bv) /\
  buffers_inv_region h bv 0ul (V.size_of bv)

val bv_inv:
  #a:Type0 -> blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> bv:buf_vector a -> GTot Type0
let bv_inv #a blen h bv =
  bv_inv_liveness blen h bv /\ bv_inv_region h bv

val buf_vector_rloc: 
  #a:Type0 -> bv:buf_vector a -> GTot loc
let buf_vector_rloc #a bv =
  B.loc_all_regions_from false (V.frameOf bv)

val loc_bv_buf_seq:
  #a:Type0 -> bs:S.seq (B.buffer a) ->
  i:nat -> j:nat{i <= j && j <= S.length bs} -> 
  GTot loc
let rec loc_bv_buf_seq #a bs i j =
  if i = j then loc_none
  else loc_union (loc_bv_buf_seq bs i (j - 1))
		 (B.loc_addr_of_buffer (S.index bs (j - 1)))

val loc_bv_buf_seq_slice_eq:
  #a:Type0 -> bs1:S.seq (B.buffer a) -> 
  bs2:S.seq (B.buffer a) ->
  i:nat -> j:nat{i <= j && j <= S.length bs1 && j <= S.length bs2} -> 
  Lemma (requires (S.equal (S.slice bs1 i j) (S.slice bs2 i j)))
	(ensures (loc_bv_buf_seq bs1 i j == loc_bv_buf_seq bs2 i j))
let rec loc_bv_buf_seq_slice_eq #a bs1 bs2 i j =
  if i = j then ()
  else (assert (S.equal (S.slice (S.slice bs1 i j) 0 (j - i - 1))
			(S.slice (S.slice bs2 i j) 0 (j - i - 1)));
       assert (S.index (S.slice bs1 i j) (j - i - 1) ==
       	      S.index (S.slice bs2 i j) (j - i - 1));
       loc_bv_buf_seq_slice_eq bs1 bs2 i (j - 1))

val loc_bv_buffers:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a -> 
  i:nat -> j:nat{i <= j && j <= U32.v (V.size_of bv)} -> 
  GTot loc
let loc_bv_buffers #a h bv i j =
  loc_bv_buf_seq (V.as_seq h bv) i j

val loc_bv_buffer:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a -> 
  i:nat{i < U32.v (V.size_of bv)} ->
  GTot loc
let loc_bv_buffer #a h bv i =
  B.loc_addr_of_buffer (S.index (V.as_seq h bv) i)

/// Specification

val as_seq_seq:
  h:HS.mem -> #a:Type -> blen:uint32_t{blen > 0ul} ->
  bslen:nat -> i:nat -> j:nat{i <= j && j <= bslen} ->
  bs:S.seq (B.buffer a){
    S.length bs = bslen /\
    V.forall_seq bs i j (fun hs -> B.len hs = blen)} ->
  GTot (s:S.seq (e:S.seq a{S.length e = U32.v blen})
       {S.length s = j - i})
       (decreases j)
let rec as_seq_seq h #a blen bslen i j bs =
  if i = j then S.empty
  else S.snoc (as_seq_seq h blen bslen i (j - 1) bs)
	      (B.as_seq h (S.index bs (j - 1)))

val as_seq:
  h:HS.mem -> #a:Type -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a{bv_inv_liveness blen h bv} ->
  GTot (s:S.seq (e:S.seq a{S.length e = U32.v blen})
       {S.length s = U32.v (V.size_of bv)})
let as_seq h #a blen bv =
  as_seq_seq h blen (U32.v (V.size_of bv)) 0 (U32.v (V.size_of bv)) (V.as_seq h bv)

val as_seq_seq_0:
  h:HS.mem -> #a:Type -> blen:uint32_t{blen > 0ul} ->
  bs:S.seq (B.buffer a) -> i:nat{i <= S.length bs} ->
  Lemma (as_seq_seq h blen (S.length bs) i i bs == S.empty)
let as_seq_seq_0 h #a blen bs i = ()

val as_seq_seq_rec:
  h:HS.mem -> #a:Type -> blen:uint32_t{blen > 0ul} ->
  bslen:nat -> i:nat -> j:nat{i <= j && j <= bslen} ->
  bs:S.seq (B.buffer a){
    S.length bs = bslen /\
    V.forall_seq bs i j (fun hs -> B.len hs = blen)} ->
  Lemma (requires (i <> j))
	(ensures (as_seq_seq h blen bslen i j bs ==
		 S.snoc (as_seq_seq h blen bslen i (j - 1) bs)
			(B.as_seq h (S.index bs (j - 1)))))
let as_seq_seq_rec h #a blen bslen i j bs = ()

val as_seq_seq_get:
  h:HS.mem -> #a:Type -> blen:uint32_t{blen > 0ul} ->
  bslen:nat -> i:nat -> j:nat{i <= j && j <= bslen} ->
  bs:S.seq (B.buffer a){
    S.length bs = bslen /\
    V.forall_seq bs i j (fun hs -> B.len hs = blen)} ->
  k:nat{i <= k && k < j} ->
  Lemma (requires True)
	(ensures (B.as_seq h (S.index bs k) == 
		 S.index (as_seq_seq h blen bslen i j bs) (k - i)))
	(decreases j)
let rec as_seq_seq_get h #a blen bslen i j bs k =
  if i = j then ()
  else if k = j - 1
  then (as_seq_seq_rec h blen bslen i j bs;
       assert (as_seq_seq h blen bslen i j bs ==
       	      S.snoc (as_seq_seq h blen bslen i (j - 1) bs)
       		     (B.as_seq h (S.index bs (j - 1)))))
  else (as_seq_seq_rec h blen bslen i j bs;
       assert (as_seq_seq h blen bslen i j bs ==
    	      S.snoc (as_seq_seq h blen bslen i (j - 1) bs)
    		     (B.as_seq h (S.index bs (j - 1))));
       as_seq_seq_get h blen bslen i (j - 1) bs k)

val as_seq_get:
  h:HS.mem -> #a:Type -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a{bv_inv_liveness blen h bv} ->
  i:uint32_t{i < V.size_of bv} ->
  Lemma (B.as_seq h (V.get h bv i) == 
	S.index (as_seq h blen bv) (U32.v i))
	[SMTPat (S.index (as_seq h blen bv) (U32.v i))]
let as_seq_get h #a blen bv i =
  as_seq_seq_get h blen (U32.v (V.size_of bv)) 0 (U32.v (V.size_of bv))
		 (V.as_seq h bv) (U32.v i)

/// Facts related to the invariant

val buf_vector_rloc_includes_loc_bv_buffer:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  Lemma (requires (bv_inv_region h bv))
	(ensures (forall (i:nat{i < U32.v (V.size_of bv)}).
	  loc_includes (buf_vector_rloc bv) (loc_bv_buffer h bv i)))
let buf_vector_rloc_includes_loc_bv_buffer #a h bv = ()

val buf_vector_rloc_includes_loc_vector:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  Lemma (loc_includes (buf_vector_rloc bv) (V.loc_addr_of_vector bv))
let buf_vector_rloc_includes_loc_vector #a h bv = ()

val buf_vector_rloc_includes_loc_bv_buffers:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  i:nat -> j:nat{i <= j && j <= U32.v (V.size_of bv)} -> 
  Lemma (requires (bv_inv_region h bv))
	(ensures (loc_includes (buf_vector_rloc bv) 
			       (loc_bv_buffers h bv i j)))
let rec buf_vector_rloc_includes_loc_bv_buffers #a h bv i j =
  if i = j then ()
  else (buf_vector_rloc_includes_loc_bv_buffers h bv i (j - 1);
       loc_includes_union_r (buf_vector_rloc bv)
			    (loc_bv_buffers h bv i (j - 1))
			    (loc_bv_buffer h bv (j - 1)))

val loc_vector_loc_bv_buffer_disjoint:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  Lemma (requires (bv_inv_region h bv))
	(ensures (forall (i:nat{i < U32.v (V.size_of bv)}).
	  loc_disjoint (V.loc_addr_of_vector bv) (loc_bv_buffer h bv i)))
let loc_vector_loc_bv_buffer_disjoint #a h bv = ()

val loc_vector_loc_bv_buffers_disjoint:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  i:nat -> j:nat{i <= j && j <= U32.v (V.size_of bv)} -> 
  Lemma (requires (bv_inv_region h bv))
	(ensures (loc_disjoint (V.loc_addr_of_vector bv) (loc_bv_buffers h bv i j)))
let rec loc_vector_loc_bv_buffers_disjoint #a h bv i j =
  if i = j then ()
  else (loc_vector_loc_bv_buffers_disjoint h bv i (j - 1);
       loc_disjoint_union_r (V.loc_addr_of_vector bv)
			    (loc_bv_buffers h bv i (j - 1))
			    (loc_bv_buffer h bv (j - 1)))

val loc_bv_buffer_disjoint:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  i:nat{i < U32.v (V.size_of bv)} -> 
  j:nat{j < U32.v (V.size_of bv) && i <> j} -> 
  Lemma (requires (bv_inv_region h bv))
	(ensures (loc_disjoint (loc_bv_buffer h bv i) (loc_bv_buffer h bv j)))
let loc_bv_buffer_disjoint #a h bv i j =
  V.forall2_seq_ok 
    (V.as_seq h bv) 0 (U32.v (V.size_of bv)) i j
    (fun b1 b2 -> HH.disjoint (B.frameOf b1) (B.frameOf b2))

val loc_bv_buffer_loc_bv_buffers_disjoint:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  i:nat -> j:nat{i <= j && j <= U32.v (V.size_of bv)} ->
  k:nat{(k < i || j <= k) && k < U32.v (V.size_of bv)} ->
  Lemma (requires (bv_inv_region h bv))
	(ensures (loc_disjoint (loc_bv_buffer h bv k) (loc_bv_buffers h bv i j)))
let rec loc_bv_buffer_loc_bv_buffers_disjoint #a h bv i j k =
  if i = j then ()
  else (loc_bv_buffer_loc_bv_buffers_disjoint h bv i (j - 1) k;
       loc_bv_buffer_disjoint h bv k (j - 1);
       loc_disjoint_union_r (loc_bv_buffer h bv k)
			    (loc_bv_buffers h bv i (j - 1))
			    (loc_bv_buffer h bv (j - 1)))

val buffers_inv_liveness_preserved:
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of bv} ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (V.live h0 bv /\
		  buffers_inv_liveness blen h0 bv i j /\ 
		  loc_disjoint (V.loc_addr_of_vector bv) dloc /\
		  loc_disjoint (loc_bv_buffers h0 bv (U32.v i) (U32.v j)) dloc /\
		  modifies dloc h0 h1))
	(ensures (buffers_inv_liveness blen h1 bv i j))
	(decreases (U32.v j))
let rec buffers_inv_liveness_preserved #a blen bv i j dloc h0 h1 =
  if i = j then ()
  else buffers_inv_liveness_preserved blen bv i (j - 1ul) dloc h0 h1

val buffers_inv_region_preserved:
  #a:Type0 -> bv:buf_vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of bv} ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (V.live h0 bv /\
		  buffers_inv_region h0 bv i j /\ 
		  loc_disjoint (V.loc_addr_of_vector bv) dloc /\
		  modifies dloc h0 h1))
	(ensures (buffers_inv_region h1 bv i j))
	(decreases (U32.v j))
let rec buffers_inv_region_preserved #a bv i j dloc h0 h1 =
  if i = j then ()
  else buffers_inv_region_preserved bv i (j - 1ul) dloc h0 h1

val bv_inv_preserved:
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (bv_inv blen h0 bv /\ 
		  loc_disjoint (buf_vector_rloc bv) dloc /\
		  modifies dloc h0 h1))
	(ensures (bv_inv blen h1 bv))
	[SMTPat (bv_inv blen h0 bv);
	SMTPat (loc_disjoint (buf_vector_rloc bv) dloc);
	SMTPat (modifies dloc h0 h1)]
let bv_inv_preserved #a blen bv dloc h0 h1 =
  buf_vector_rloc_includes_loc_vector h0 bv;
  buf_vector_rloc_includes_loc_bv_buffers h0 bv 0 (U32.v (V.size_of bv));

  buffers_inv_liveness_preserved blen bv 0ul (V.size_of bv) dloc h0 h1;
  buffers_inv_region_preserved bv 0ul (V.size_of bv) dloc h0 h1

val loc_bv_buffers_as_seq:
  #a:Type0 -> h0:HS.mem -> h1:HS.mem ->
  bv:buf_vector a ->
  i:nat -> j:nat{i <= j && j <= U32.v (V.size_of bv)} ->
  Lemma (requires (V.as_seq h0 bv == V.as_seq h1 bv))
	(ensures (loc_bv_buffers h0 bv i j == loc_bv_buffers h1 bv i j))
let rec loc_bv_buffers_as_seq #a h0 h1 bv i j =
  if i = j then ()
  else loc_bv_buffers_as_seq h0 h1 bv i (j - 1)

val as_seq_seq_preserved:
  #a:Type -> blen:uint32_t{blen > 0ul} ->
  bslen:nat -> i:nat -> j:nat{i <= j && j <= bslen} ->
  bs:S.seq (B.buffer a){
    S.length bs = bslen /\
    V.forall_seq bs i j (fun hs -> B.len hs = blen)} ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (V.forall_seq bs 0 (S.length bs) (fun hs -> B.live h0 hs) /\
		  loc_disjoint (loc_bv_buf_seq bs i j) dloc /\
		  modifies dloc h0 h1))
	(ensures (S.equal (as_seq_seq h0 blen bslen i j bs)
			  (as_seq_seq h1 blen bslen i j bs)))
	(decreases j)
let rec as_seq_seq_preserved #a blen bslen i j bs dloc h0 h1 =
  if i = j
  then (as_seq_seq_0 h0 blen bs i; as_seq_seq_0 h1 blen bs i)
  else (as_seq_seq_preserved blen bslen i (j - 1) bs dloc h0 h1;
       as_seq_seq_rec h0 blen bslen i j bs;
       assert (as_seq_seq h0 blen bslen i j bs ==
       	      S.snoc (as_seq_seq h0 blen bslen i (j - 1) bs)
       		     (B.as_seq h0 (S.index bs (j - 1))));
       as_seq_seq_rec h1 blen bslen i j bs;
       assert (as_seq_seq h1 blen bslen i j bs ==
       	      S.snoc (as_seq_seq h1 blen bslen i (j - 1) bs)
       		     (B.as_seq h1 (S.index bs (j - 1))));
       modifies_buffer_elim (S.index bs (j - 1)) dloc h0 h1)

val as_seq_preserved:
  #a:Type -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (bv_inv blen h0 bv /\ 
		  loc_disjoint (buf_vector_rloc bv) dloc /\
		  modifies dloc h0 h1))
	(ensures (S.equal (as_seq h0 blen bv) (as_seq h1 blen bv)))
	[SMTPat (bv_inv blen h0 bv);
	SMTPat (loc_disjoint (buf_vector_rloc bv) dloc);
	SMTPat (modifies dloc h0 h1)]
let as_seq_preserved #a blen bv dloc h0 h1 =
  buf_vector_rloc_includes_loc_vector h0 bv;
  buf_vector_rloc_includes_loc_bv_buffers h0 bv 0 (U32.v (V.size_of bv));
  as_seq_seq_preserved blen (U32.v (V.size_of bv)) 
		       0 (U32.v (V.size_of bv)) (V.as_seq h0 bv) dloc h0 h1

/// Construction

private val create_:
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  ia:a -> bv:buf_vector a ->
  cidx:uint32_t{cidx <= V.size_of bv} -> 
  HST.ST unit
    (requires (fun h0 -> 
      V.live h0 bv /\ V.freeable bv /\
      HST.is_eternal_region (V.frameOf bv)))
    (ensures (fun h0 _ h1 ->
      modifies (V.loc_vector_within bv 0ul cidx) h0 h1 /\
      // partial liveness
      V.live h0 bv /\ V.freeable bv /\
      buffers_inv_liveness blen h1 bv 0ul cidx /\
      // partial region
      HST.is_eternal_region (V.frameOf bv) /\
      buffers_inv_region h1 bv 0ul cidx /\
      // loop invariants for this function
      V.forall_ h1 bv 0ul cidx
      	(fun b -> MHS.fresh_region (B.frameOf b) h0 h1) /\
      // correctness
      S.equal (as_seq_seq h1 blen (U32.v (V.size_of bv)) 
			  0 (U32.v cidx) (V.as_seq h1 bv))
	      (S.create (U32.v cidx) (S.create (U32.v blen) ia))))
    (decreases (U32.v cidx))
private let rec create_ #a blen ia bv cidx =
  if cidx = 0ul then ()
  else (let hh0 = HST.get () in
       let nrid = new_region_ (V.frameOf bv) in

       V.assign bv (cidx - 1ul) (B.malloc nrid ia blen);

       let hh1 = HST.get () in
       assert (nrid = B.frameOf (V.get hh1 bv (cidx - 1ul)));
       assert (Set.equal
	        (Map.domain (MHS.get_hmap hh1))
		(Set.union (Map.domain (MHS.get_hmap hh0)) 
			   (Set.singleton nrid)));

       create_ #a blen ia bv (cidx - 1ul);

       let hh2 = HST.get () in
       // liveness
       V.forall_preserved
	 bv (cidx - 1ul) cidx
	 (fun b -> buffer_inv_liveness blen hh1 b /\
		   HH.extends (B.frameOf b) (V.frameOf bv))
	 (V.loc_vector_within bv 0ul (cidx - 1ul))
	 hh1 hh2;

       // region
       assert (nrid = B.frameOf (V.get hh2 bv (cidx - 1ul)));
       assert (V.forall_ hh2 bv 0ul (cidx - 1ul)
       			 (fun b -> HH.disjoint (B.frameOf b) nrid));

       V.forall2_extend hh2 bv 0ul (cidx - 1ul)
       	 (fun b1 b2 -> HH.disjoint (B.frameOf b1) (B.frameOf b2)))

val create_rid:
  #a:Type0 -> ia:a -> blen:uint32_t{blen > 0ul} ->
  len:uint32_t{len > 0ul} -> rid:erid ->
  HST.ST (buf_vector a)
    (requires (fun h0 -> true))
    (ensures (fun h0 bv h1 ->
      modifies (buf_vector_rloc bv) h0 h1 /\
      bv_inv blen h1 bv /\
      V.frameOf bv = rid /\
      V.size_of bv = len /\
      S.equal (as_seq h1 blen bv) 
	      (S.create (U32.v len) (S.create (U32.v blen) ia))))
let create_rid #a ia blen len rid =
  let vec = V.create_rid len (B.null #a) rid in
  create_ #a blen ia vec len;
  vec

val create_reserve:
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  len:uint32_t{len > 0ul} -> rid:erid ->
  HST.ST (buf_vector a)
    (requires (fun h0 -> true))
    (ensures (fun h0 bv h1 ->
      modifies (buf_vector_rloc bv) h0 h1 /\
      bv_inv blen h1 bv /\
      V.frameOf bv = rid /\
      V.size_of bv = 0ul /\
      S.equal (as_seq h1 blen bv) S.empty))
let create_reserve #a blen len rid =
  V.create_reserve len (B.null #a) rid

val create:
  #a:Type0 -> ia:a -> blen:uint32_t{blen > 0ul} -> 
  len:uint32_t{len > 0ul} ->
  HST.ST (buf_vector a)
    (requires (fun h0 -> true))
    (ensures (fun h0 bv h1 ->
      modifies (buf_vector_rloc bv) h0 h1 /\
      bv_inv blen h1 bv /\
      MHS.fresh_region (V.frameOf bv) h0 h1 /\
      V.size_of bv = len /\
      S.equal (as_seq h1 blen bv)
	      (S.create (U32.v len) (S.create (U32.v blen) ia))))
let create #a ia blen len =
  let nrid = new_region_ root in
  create_rid ia blen len nrid

val insert_copy:
  #a:Type0 -> ia:a -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a{not (V.is_full bv)} ->
  v:B.buffer a ->
  HST.ST (buf_vector a)
    (requires (fun h0 -> 
      bv_inv blen h0 bv /\ buffer_inv_liveness blen h0 v))
    (ensures (fun h0 ibv h1 ->
      V.frameOf bv = V.frameOf ibv /\
      modifies (buf_vector_rloc bv) h0 h1 /\
      bv_inv blen h1 ibv /\
      S.equal (as_seq h1 blen ibv) (S.snoc (as_seq h0 blen bv) (B.as_seq h0 v))))
#set-options "--z3rlimit 40"
let insert_copy #a ia blen bv v =
  let nrid = new_region_ (V.frameOf bv) in
  let nv = B.malloc nrid ia blen in
  B.blit v 0ul nv 0ul blen;
  let ibv = V.insert bv nv in
  admit ();
  ibv

val assign_copy:
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a ->
  i:uint32_t{i < V.size_of bv} -> v:B.buffer a ->
  HST.ST unit
    (requires (fun h0 ->
      bv_inv blen h0 bv /\ buffer_inv_liveness blen h0 v /\
      HH.disjoint (V.frameOf bv) (B.frameOf v)))
    (ensures (fun h0 _ h1 -> 
      modifies (buf_vector_rloc bv) h0 h1 /\
      bv_inv blen h1 bv /\
      S.equal (as_seq h1 blen bv)
	      (S.upd (as_seq h0 blen bv) (U32.v i) (B.as_seq h0 v))))
let assign_copy #a blen bv i v =
  B.blit v 0ul (V.index bv i) 0ul blen;
  admit ()

val free_bufs:
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a ->
  idx:uint32_t{idx < V.size_of bv} ->
  HST.ST unit
    (requires (fun h0 -> 
      V.live h0 bv /\
      buffers_inv_liveness blen h0 bv 0ul (idx + 1ul) /\
      bv_inv_region h0 bv))
    (ensures (fun h0 _ h1 ->
      modifies (loc_bv_buffers h0 bv 0 (U32.v idx + 1)) h0 h1))
let rec free_bufs #a blen bv idx =
  let hh0 = HST.get () in
  loc_bv_buffer_loc_bv_buffers_disjoint hh0 bv 0 (U32.v idx) (U32.v idx);

  B.free (V.index bv idx);

  let hh1 = HST.get () in
  if idx <> 0ul then
    (loc_bv_buffers_as_seq hh0 hh1 bv 0 (U32.v idx);
    buffers_inv_liveness_preserved blen bv 0ul idx (loc_bv_buffer hh0 bv (U32.v idx)) hh0 hh1;
    free_bufs blen bv (idx - 1ul))

val free: 
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a ->
  HST.ST unit
    (requires (fun h0 -> bv_inv blen h0 bv))
    (ensures (fun h0 _ h1 -> modifies (buf_vector_rloc bv) h0 h1))
let free #a blen bv =
  let hh0 = HST.get () in
  (if V.size_of bv = 0ul then () else free_bufs blen bv (V.size_of bv - 1ul));

  buf_vector_rloc_includes_loc_bv_buffers hh0 bv 0 (U32.v (V.size_of bv));
  buf_vector_rloc_includes_loc_vector hh0 bv;
  loc_vector_loc_bv_buffers_disjoint hh0 bv 0 (U32.v (V.size_of bv));

  V.free bv

