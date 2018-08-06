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

/// Facts related to the invariant

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
  admit ()

/// Construction

private val create_:
  #a:Type0 -> #blen:uint32_t{blen > 0ul} ->
  ia:a -> bv:buf_vector a ->
  cidx:uint32_t{cidx <= V.size_of bv} -> 
  HST.ST unit
    (requires (fun h0 -> 
      V.live h0 bv /\ V.freeable bv /\
      HST.is_eternal_region (V.frameOf bv)))
    (ensures (fun h0 _ h1 ->
      // Only the vector elements are changed.
      V.live h0 bv /\ V.freeable bv /\
      HST.is_eternal_region (V.frameOf bv) /\
      modifies (V.loc_vector_within bv 0ul cidx) h0 h1 /\

      // The elements are `malloc`ed pointers in a subregion 
      // of the vector region.
      V.forall_ h1 bv 0ul cidx
	(fun b -> B.live h1 b /\ B.len b = blen /\ B.freeable b) /\
      V.forall_ h1 bv 0ul cidx
	(fun b -> HH.extends (B.frameOf b) (V.frameOf bv) /\ 
		  B.frameOf b <> V.frameOf bv) /\
      V.forall2 h1 bv 0ul cidx
	(fun b1 b2 -> B.frameOf b1 <> B.frameOf b2)))
    (decreases (U32.v cidx))
private let rec create_ #a #blen ia bv cidx =
  if cidx = 0ul then ()
  else (let nrid = new_region_ (V.frameOf bv) in
       V.assign bv (cidx - 1ul) (B.malloc nrid ia blen);

       let hh1 = HST.get () in
       create_ #a #blen ia bv (cidx - 1ul);

       let hh2 = HST.get () in
       // `V.forall_` properties for a single assignment is automatically
       // verified, but need to prove that such properties are preserved
       // after disjoint state transitions.
       V.forall_disjoint_not_affected
	 bv (cidx - 1ul) cidx
	 (fun b -> B.live hh1 b /\ B.len b = blen /\ B.freeable b /\
		   HH.extends (B.frameOf b) (V.frameOf bv) /\ 
       		   B.frameOf b <> V.frameOf bv)
	 (V.loc_vector_within bv 0ul (cidx - 1ul))
	 hh1 hh2;

       assume (V.forall_ hh2 bv 0ul (cidx - 1ul)
	      (fun b -> B.frameOf b <> B.frameOf (V.get hh2 bv (cidx - 1ul)) /\
			B.frameOf (V.get hh2 bv (cidx - 1ul)) <> B.frameOf b));
       V.forall2_extend hh2 bv 0ul (cidx - 1ul)
	 (fun b1 b2 -> B.frameOf b1 <> B.frameOf b2))

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
  create_ #a #blen ia vec len;
  admit ();
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
      buffer_inv_liveness blen h0 v /\ bv_inv blen h0 bv))
    (ensures (fun h0 ibv h1 -> 
      V.frameOf bv = V.frameOf ibv /\
      modifies (buf_vector_rloc bv) h0 h1 /\
      bv_inv blen h1 ibv /\
      buffer_inv_liveness blen h1 v))
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
      buffer_inv_liveness blen h0 v /\ bv_inv blen h0 bv))
    (ensures (fun h0 _ h1 -> 
      modifies (buf_vector_rloc bv) h0 h1 /\
      bv_inv blen h1 bv))
let assign_copy #a blen bv i v =
  let iv = V.index bv i in
  admit (); B.blit v 0ul iv 0ul blen

val free_bufs:
  #a:Type0 -> blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a ->
  idx:uint32_t{idx < V.size_of bv} ->
  HST.ST unit
    (requires (fun h0 -> bv_inv blen h0 bv))
    (ensures (fun h0 _ h1 -> modifies (buf_vector_rloc bv) h0 h1))
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
  (if V.size_of bv = 0ul then () else free_bufs blen bv (V.size_of bv - 1ul));
  admit (); V.free bv

