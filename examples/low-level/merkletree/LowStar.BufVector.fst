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

/// The invariant

val buffer_inv_liveness:
  #a:Type0 -> blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> b:B.buffer a -> GTot Type0
let buffer_inv_liveness #a blen h b =
  B.live h b /\ B.len b = blen /\ B.freeable b

val bv_inv_liveness:
  #a:Type0 -> blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> bv:buf_vector a -> GTot Type0
let bv_inv_liveness #a blen h bv =
  V.live h bv /\ V.freeable bv /\
  V.forall_all h bv (buffer_inv_liveness blen h)

val bv_inv_region:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a -> GTot Type0
let bv_inv_region #a h bv =
  HST.is_eternal_region (V.frameOf bv) /\
  V.forall_all h bv 
    (fun b -> HH.extends (B.frameOf b) (V.frameOf bv)) /\
  V.forall2_all h bv
    (fun b1 b2 -> HH.disjoint (B.frameOf b1) (B.frameOf b2))

val bv_inv:
  #a:Type0 -> blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> bv:buf_vector a -> GTot Type0
let bv_inv #a blen h bv =
  bv_inv_liveness blen h bv /\ bv_inv_region h bv

val buf_vector_rloc: 
  #a:Type0 -> bv:buf_vector a -> GTot loc
let buf_vector_rloc #a bv =
  B.loc_all_regions_from false (V.frameOf bv)

val loc_buffer:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a -> 
  i:nat{i < U32.v (V.size_of bv)} -> GTot loc
let loc_buffer #a h bv i =
  B.loc_buffer (S.index (V.as_seq h bv) i)

val loc_buffers:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a -> 
  i:nat -> j:nat{i <= j && j <= U32.v (V.size_of bv)} -> 
  GTot loc
let rec loc_buffers #a h bv i j =
  if i = j then loc_none
  else loc_union (loc_buffers h bv i (j - 1))
		 (loc_buffer h bv (j - 1))

/// Facts related to the invariant

val buf_vector_rloc_includes_loc_buffer:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  Lemma (requires (bv_inv_region h bv))
	(ensures (forall (i:nat{i < U32.v (V.size_of bv)}).
	  loc_includes (buf_vector_rloc bv) (loc_buffer h bv i)))
let buf_vector_rloc_includes_loc_buffer #a h bv = ()

val buf_vector_rloc_includes_loc_vector:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  Lemma (loc_includes (buf_vector_rloc bv) (V.loc_vector bv))
let buf_vector_rloc_includes_loc_vector #a h bv = ()

val buf_vector_rloc_includes_loc_buffers:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  i:nat -> j:nat{i <= j && j <= U32.v (V.size_of bv)} -> 
  Lemma (requires (bv_inv_region h bv))
	(ensures (loc_includes (buf_vector_rloc bv) 
			       (loc_buffers h bv i j)))
let rec buf_vector_rloc_includes_loc_buffers #a h bv i j =
  if i = j then ()
  else (buf_vector_rloc_includes_loc_buffers h bv i (j - 1);
       loc_includes_union_r (buf_vector_rloc bv)
			    (loc_buffers h bv i (j - 1))
			    (loc_buffer h bv (j - 1)))

val loc_vector_loc_buffer_disjoint:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  Lemma (requires (bv_inv_region h bv))
	(ensures (forall (i:nat{i < U32.v (V.size_of bv)}).
	  loc_disjoint (V.loc_vector bv) (loc_buffer h bv i)))
let loc_vector_loc_buffer_disjoint #a h bv = ()

val loc_vector_loc_buffers_disjoint:
  #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
  i:nat -> j:nat{i <= j && j <= U32.v (V.size_of bv)} -> 
  Lemma (requires (bv_inv_region h bv))
	(ensures (loc_disjoint (V.loc_vector bv) (loc_buffers h bv i j)))
let rec loc_vector_loc_buffers_disjoint #a h bv i j =
  if i = j then ()
  else (loc_vector_loc_buffers_disjoint h bv i (j - 1);
       loc_disjoint_union_r (V.loc_vector bv)
			    (loc_buffers h bv i (j - 1))
			    (loc_buffer h bv (j - 1)))

// val loc_buffer_loc_buffers_disjoint:
//   #a:Type0 -> h:HS.mem -> bv:buf_vector a ->
//   i:nat -> j:nat{i <= j && j <= U32.v (V.size_of bv)} ->
//   k:nat{(k < i || j <= k) && k < U32.v (V.size_of bv)} ->
//   Lemma (requires (bv_inv_region h bv))
// 	(ensures (loc_disjoint (loc_buffer h bv k) (loc_buffers h bv i j)))
// let rec loc_buffer_loc_buffers_disjoint #a h bv i j k =
//   if i = j then ()
//   else (loc_buffer_loc_buffers_disjoint h bv i (j - 1) k;
//        loc_disjoint_union_r (loc_buffer h bv k)
// 			    (loc_buffers h bv i (j - 1))
// 			    (loc_buffer h bv (j - 1)))

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
  buf_vector_rloc_includes_loc_buffer h0 bv;

  // liveness
  assert (forall (i:nat{i < (U32.v (V.size_of bv))}).
  	 buffer_inv_liveness blen h1 (S.index (V.as_seq h1 bv) i));
  assert (V.forall_all h1 bv (buffer_inv_liveness blen h1));

  // region
  V.forall_all_preserved 
    bv (fun b -> HH.extends (B.frameOf b) (V.frameOf bv)) dloc h0 h1;
  V.forall2_all_preserved
    bv (fun b1 b2 -> HH.disjoint (B.frameOf b1) (B.frameOf b2)) dloc h0 h1

/// Construction

val modifies_fresh_region:
  h0:HS.mem -> h1:HS.mem -> h2:HS.mem ->
  r:HH.rid -> s:loc ->
  Lemma (requires (MHS.fresh_region r h0 h1 /\
		  modifies s h1 h2 /\ 
		  loc_disjoint s (loc_region_only false r)))
	(ensures (MHS.fresh_region r h0 h2))
let modifies_fresh_region h0 h1 h2 r s =
  admit ()

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

      // liveness
      V.live h0 bv /\ V.freeable bv /\
      V.forall_ h1 bv 0ul cidx (buffer_inv_liveness blen h1) /\

      // region
      HST.is_eternal_region (V.frameOf bv) /\
      V.forall_ h1 bv 0ul cidx
	(fun b -> HH.extends (B.frameOf b) (V.frameOf bv)) /\
      V.forall2 h1 bv 0ul cidx
	(fun b1 b2 -> HH.disjoint (B.frameOf b1) (B.frameOf b2)) /\

      // loop invariants for this function
      V.forall_ h1 bv 0ul cidx
      	(fun b -> MHS.fresh_region (B.frameOf b) h0 h1)))
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
      V.size_of bv = len))
let create_rid #a ia blen len rid =
  let vec = V.create_rid len (B.null #a) rid in
  create_ #a blen ia vec len;
  vec

val create:
  #a:Type0 -> ia:a -> blen:uint32_t{blen > 0ul} -> 
  len:uint32_t{len > 0ul} ->
  HST.ST (buf_vector a)
    (requires (fun h0 -> true))
    (ensures (fun h0 bv h1 ->
      modifies (buf_vector_rloc bv) h0 h1 /\
      bv_inv blen h1 bv /\
      MHS.fresh_region (V.frameOf bv) h0 h1 /\
      V.size_of bv = len))
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
      bv_inv blen h1 ibv /\ buffer_inv_liveness blen h1 v))
let insert_copy #a ia blen bv v =
  let nrid = new_region_ (V.frameOf bv) in
  let nv = B.malloc nrid ia blen in
  B.blit v 0ul nv 0ul blen;
  admit (); V.insert bv nv

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
      bv_inv blen h1 bv))
let assign_copy #a blen bv i v =
  B.blit v 0ul (V.index bv i) 0ul blen

val free_bufs:
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a ->
  idx:uint32_t{idx < V.size_of bv} ->
  HST.ST unit
    (requires (fun h0 -> 
      V.live h0 bv /\
      V.forall_ h0 bv 0ul (idx + 1ul) (buffer_inv_liveness blen h0) /\
      V.forall_ h0 bv 0ul (idx + 1ul) 
	(fun b -> HH.extends (B.frameOf b) (V.frameOf bv)) /\
      V.forall2 h0 bv 0ul (idx + 1ul)
	(fun b1 b2 -> HH.disjoint (B.frameOf b1) (B.frameOf b2))))
    (ensures (fun h0 _ h1 ->
      modifies (loc_buffers h0 bv 0 (U32.v idx + 1)) h0 h1))
let rec free_bufs #a blen bv idx =
  admit ();
  B.free (V.index bv idx);
  if idx <> 0ul then
    free_bufs blen bv (idx - 1ul)

val free: 
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a ->
  HST.ST unit
    (requires (fun h0 -> bv_inv blen h0 bv))
    (ensures (fun h0 _ h1 -> modifies (buf_vector_rloc bv) h0 h1))
let free #a blen bv =
  let hh0 = HST.get () in
  (if V.size_of bv = 0ul then () else free_bufs blen bv (V.size_of bv - 1ul));

  buf_vector_rloc_includes_loc_buffers hh0 bv 0 (U32.v (V.size_of bv));
  buf_vector_rloc_includes_loc_vector hh0 bv;
  loc_vector_loc_buffers_disjoint hh0 bv 0 (U32.v (V.size_of bv));

  V.free bv

