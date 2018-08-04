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

type lbuf a (blen:uint32_t{blen > 0ul}) = 
  b:B.buffer a{B.g_is_null b \/ B.len b = blen}
type buf_vector a blen = V.vector (lbuf a blen)

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

val bv_inv_liveness:
  #a:Type0 -> #blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> bv:buf_vector a blen -> GTot Type0
let bv_inv_liveness #a #blen h bv =
  V.live h bv /\ V.freeable bv /\
  V.forall_prop h bv 
    (fun b -> B.live h b /\ (B.g_is_null b \/ B.freeable b))

val bv_inv_region:
  #a:Type0 -> #blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> bv:buf_vector a blen -> GTot Type0
let bv_inv_region #a #blen h bv =
  HST.is_eternal_region (V.frameOf bv) /\
  V.forall_prop h bv 
    (fun b -> 
      B.g_is_null b \/
      (HH.extends (B.frameOf b) (V.frameOf bv) /\ 
      B.frameOf b <> V.frameOf bv)) /\
  V.forall_two_prop h bv
    (fun b1 b2 -> 
      B.g_is_null b1 \/ B.g_is_null b2 \/
      B.frameOf b1 <> B.frameOf b2)

val bv_inv:
  #a:Type0 -> #blen:uint32_t{blen > 0ul} -> 
  h:HS.mem -> bv:buf_vector a blen -> GTot Type0
let bv_inv #a #blen h bv =
  bv_inv_liveness h bv /\
  bv_inv_region h bv

val buf_vector_loc: 
  #a:Type0 -> #blen:uint32_t{blen > 0ul} -> 
  bv:buf_vector a blen -> GTot loc
let buf_vector_loc #a #blen bv =
  B.loc_regions false (FStar.Set.singleton (V.frameOf bv))

/// Facts related to the invariant

// val bv_inv_extend:
//   #a:Type0 -> #blen:uint32_t{blen > 0ul} -> 
//   h:HS.mem -> bv:buf_vector a blen ->
//   v:lbuf a blen ->
//   Lemma (requires (bv_inv h bv))
// 	(ensures (bv_inv h (V.insert bv v)))

/// Construction

val create_rid:
  #a:Type0 -> #blen:uint32_t{blen > 0ul} -> 
  len:uint32_t{len > 0ul} -> rid:erid ->
  HST.ST (buf_vector a blen)
    (requires (fun h0 -> true))
    (ensures (fun h0 bv h1 ->
      bv_inv h1 bv /\
      V.frameOf bv = rid /\
      modifies loc_none h0 h1 /\
      V.size_of bv = len))
let create_rid #a #blen len rid =
  V.create_rid len (B.null #a) rid

val create:
  #a:Type0 -> #blen:uint32_t{blen > 0ul} -> 
  len:uint32_t{len > 0ul} ->
  HST.ST (buf_vector a blen)
    (requires (fun h0 -> true))
    (ensures (fun h0 bv h1 ->
      bv_inv h1 bv /\
      MHS.fresh_region (V.frameOf bv) h0 h1 /\
      modifies loc_none h0 h1 /\
      V.size_of bv = len))
let create #a #blen len =
  let nrid = new_region_ root in
  let hh1 = HST.get () in
  let bv = create_rid #a #blen len nrid in
  let hh2 = HST.get () in
  B.modifies_live_region loc_none hh1 hh2 nrid;
  bv
  
// insert_pointer: ...

val insert_copy:
  #a:Type0 -> ia:a -> #blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a blen{not (V.is_full bv)} ->
  v:lbuf a blen ->
  HST.ST (buf_vector a blen)
    (requires (fun h0 -> 
      B.live h0 v /\ not (B.g_is_null v) /\
      bv_inv h0 bv))
    (ensures (fun h0 ibv h1 -> 
      bv_inv h1 ibv))
let insert_copy #a ia #blen bv v =
  let nrid = new_region_ (V.frameOf bv) in
  let nv = B.malloc nrid ia blen in
  B.blit v 0ul nv 0ul blen;
  admit (); V.insert bv nv

val assign_copy:
  #a:Type0 -> ia:a -> #blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a blen ->
  i:uint32_t{i < V.size_of bv} ->
  v:lbuf a blen ->
  HST.ST unit
    (requires (fun h0 -> 
      B.live h0 v /\ not (B.g_is_null v) /\
      bv_inv h0 bv))
    (ensures (fun h0 _ h1 -> 
      bv_inv h1 bv))
let assign_copy #a ia #blen bv i v =
  let iv = V.index bv i in
  if B.is_null iv 
  then (let nrid = new_region_ (V.frameOf bv) in
       let nv = B.malloc nrid ia blen in
       B.blit v 0ul nv 0ul blen;
       admit (); V.assign bv i nv)
  else (admit (); B.blit v 0ul iv 0ul blen)

val free_bufs:
  #a:Type0 -> #blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a blen ->
  idx:uint32_t{idx < V.size_of bv} ->
  HST.ST unit
    (requires (fun h0 -> bv_inv h0 bv))
    (ensures (fun h0 _ h1 -> true))
let rec free_bufs #a #blen bv idx =
  admit ();
  B.free (V.index bv idx);
  if idx <> 0ul then
    free_bufs bv (idx - 1ul)

val free: 
  #a:Type0 -> #blen:uint32_t{blen > 0ul} ->
  bv:buf_vector a blen ->
  HST.ST unit
    (requires (fun h0 -> bv_inv h0 bv))
    (ensures (fun h0 _ h1 -> modifies (buf_vector_loc bv) h0 h1))
let free #a #blen bv =
  (if V.size_of bv = 0ul then () else free_bufs bv (V.size_of bv - 1ul));
  admit ();
  V.free bv

