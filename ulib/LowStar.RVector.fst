module LowStar.RVector

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

/// Regionality

type erid = rid:HH.rid{HST.is_eternal_region rid}

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

noeq type regional a =
| Rgl:
    region_of: (a -> GTot HH.rid) ->
    r_live: (HS.mem -> a -> GTot Type0) ->
    r_live_preserved:
      (v:a -> p:loc -> h:HS.mem -> h':HS.mem ->
      Lemma (requires (loc_disjoint (loc_region_only false (region_of v)) p /\
		      r_live h v /\ modifies p h h'))
	    (ensures (r_live h' v))) -> // /\ r_repr h v == r_repr h' v))) ->
    r_freeable: (a -> GTot Type0) ->
    r_create: (r:erid ->
      HST.ST a
	(requires (fun h0 -> true))
	(ensures (fun h0 v h1 -> 
	  modifies loc_none h0 h1 /\
	  r_live h1 v /\ r_freeable v /\
	  region_of v = r))) ->
    r_copy: (src:a -> dst:a ->
      HST.ST unit
	(requires (fun h0 -> true))
	(ensures (fun h0 _ h1 ->
	  modifies (loc_region_only false (region_of dst)) h0 h1 /\
	  r_live h1 dst /\ r_freeable dst))) ->
	  // /\ r_repr h1 cv == r_repr h0 v))
    r_free: (v:a ->
      HST.ST unit
	(requires (fun h0 -> r_live h0 v /\ r_freeable v))
	(ensures (fun h0 _ h1 ->
	  modifies (loc_region_only false (region_of v)) h0 h1))) ->
    regional a

val loc_region_rg: 
  #a:Type -> rg:regional a -> v:a -> GTot loc
let loc_region_rg #a rg v =
  loc_region_only false (Rgl?.region_of rg v)

type rvector #a (rg:regional a) = V.vector a

/// Invariants about liveness and regional disjointness

// About liveness

val elem_live:
  #a:Type0 -> rg:regional a ->
  h:HS.mem -> v:a -> GTot Type0
let elem_live #a rg h v =
  Rgl?.r_live rg h v /\ Rgl?.r_freeable rg v

val elems_live:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg -> 
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} ->
  GTot Type0
let elems_live #a #rg h rv i j =
  V.forall_ h rv i j (elem_live rg h)

val rv_live:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg -> GTot Type0
let rv_live #a #rg h rv =
  V.live h rv /\ V.freeable rv /\
  elems_live h rv 0ul (V.size_of rv)

// About regional disjointness

val elems_disj:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} ->
  GTot Type0
let elems_disj #a #rg h rv i j =
  V.forall_ h rv i j
    (fun v -> HH.extends (Rgl?.region_of rg v) (V.frameOf rv)) /\
  V.forall2 h rv i j
    (fun v1 v2 -> HH.disjoint (Rgl?.region_of rg v1)
			      (Rgl?.region_of rg v2))

val rv_disj:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg -> GTot Type0
let rv_disj #a #rg h rv =
  HST.is_eternal_region (V.frameOf rv) /\
  elems_disj h rv 0ul (V.size_of rv)

// The invariant of rvector

val rv_inv:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg -> GTot Type0
let rv_inv #a #rg h rv =
  rv_live h rv /\ rv_disj #a #rg h rv

val rv_loc_only:
  #a:Type -> #rg:regional a -> rv:rvector rg -> GTot loc
let rv_loc_only #a #rg rv =
  B.loc_region_only false (V.frameOf rv)

val rv_loc_all:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> GTot loc
let rv_loc_all #a #rg rv =
  B.loc_all_regions_from false (V.frameOf rv)

val rv_loc_elem:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:nat{i < U32.v (V.size_of rv)} ->
  GTot loc
let rv_loc_elem #a #rg h rv i =
  B.loc_all_regions_from false 
    (Rgl?.region_of rg (S.index (V.as_seq h rv) i))

val rv_loc_elems:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:nat -> j:nat{i <= j && j <= U32.v (V.size_of rv)} -> 
  GTot loc
let rec rv_loc_elems #a #rg h rv i j =
  if i = j then loc_none
  else loc_union (rv_loc_elems h rv i (j - 1))
		 (rv_loc_elem h rv (j - 1))

/// Construction

val create_empty:
  a:Type0 -> rg:regional a ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 bv h1 -> h0 == h1 /\ V.size_of bv = 0ul))
let create_empty a rg =
  V.create_empty a

private val create_:
  #a:Type0 -> #rg:regional a -> rv:rvector rg ->
  cidx:uint32_t{cidx <= V.size_of rv} -> 
  HST.ST unit
    (requires (fun h0 -> 
      V.live h0 rv /\ V.freeable rv /\
      HST.is_eternal_region (V.frameOf rv)))
    (ensures (fun h0 _ h1 ->
      modifies (V.loc_vector_within rv 0ul cidx) h0 h1 /\
      // partial live
      V.live h0 rv /\ V.freeable rv /\
      elems_live h1 rv 0ul cidx /\
      // partial region
      HST.is_eternal_region (V.frameOf rv) /\
      elems_disj h1 rv 0ul cidx))
    (decreases (U32.v cidx))
private let rec create_ #a #rg rv cidx =
  admit ();
  if cidx = 0ul then ()
  else (let hh0 = HST.get () in
       let nrid = new_region_ (V.frameOf rv) in
       let v = Rgl?.r_create rg nrid in
       V.assign rv (cidx - 1ul) v;
       create_ rv (cidx - 1ul))

val create_rid:
  #a:Type0 -> rg:regional a -> ia:a ->
  len:uint32_t{len > 0ul} -> rid:erid ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 rv h1 ->
      modifies (rv_loc_only rv) h0 h1 /\
      rv_inv h1 rv /\
      V.frameOf rv = rid /\
      V.size_of rv = len))
      // S.equal (as_seq h1 blen bv) 
      // 	      (S.create (U32.v len) (S.create (U32.v blen) ia))))
let create_rid #a rg ia len rid =
  let vec = V.create_rid len ia rid in
  create_ #a #rg vec len;
  vec

val create_reserve:
  #a:Type0 -> rg:regional a -> ia:a ->
  len:uint32_t{len > 0ul} -> rid:erid ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 rv h1 ->
      modifies (rv_loc_only rv) h0 h1 /\
      rv_inv h1 rv /\
      V.frameOf rv = rid /\
      V.size_of rv = 0ul))
      // S.equal (as_seq h1 blen bv) S.empty))
let create_reserve #a rg ia len rid =
  V.create_reserve len ia rid

val create:
  #a:Type0 -> rg:regional a -> ia:a ->
  len:uint32_t{len > 0ul} ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 rv h1 ->
      modifies (rv_loc_only rv) h0 h1 /\
      rv_inv h1 rv /\
      MHS.fresh_region (V.frameOf rv) h0 h1 /\
      V.size_of rv = len))
      // S.equal (as_seq h1 blen bv)
      // 	      (S.create (U32.v len) (S.create (U32.v blen) ia))))
let create #a rg ia len =
  let nrid = new_region_ HH.root in
  create_rid rg ia len nrid

val insert_ptr:
  #a:Type0 -> #rg:regional a ->
  rv:rvector rg{not (V.is_full rv)} -> v:a ->
  HST.ST (rvector rg)
    (requires (fun h0 -> 
      rv_inv h0 rv /\ elem_live rg h0 v /\
      HH.extends (Rgl?.region_of rg v) (V.frameOf rv) /\
      V.forall_all h0 rv
	(fun b -> HH.disjoint (Rgl?.region_of rg b)
			      (Rgl?.region_of rg v))))
    (ensures (fun h0 irv h1 ->
      V.frameOf rv = V.frameOf irv /\
      modifies (rv_loc_only rv) h0 h1 /\
      rv_inv h1 irv))
      // S.equal (as_seq h1 blen ibv)
      // 	      (S.snoc (as_seq h0 blen bv) (B.as_seq h0 v))))
#set-options "--z3rlimit 40"
let insert_ptr #a #rg rv v =
  admit ();
  V.insert rv v

val insert_copy:
  #a:Type0 -> #rg:regional a ->
  rv:rvector rg{not (V.is_full rv)} -> v:a ->
  HST.ST (rvector rg)
    (requires (fun h0 -> rv_inv h0 rv /\ elem_live rg h0 v))
    (ensures (fun h0 irv h1 ->
      V.frameOf rv = V.frameOf irv /\
      modifies (rv_loc_all rv) h0 h1 /\
      rv_inv h1 irv))
      // S.equal (as_seq h1 blen ibv)
      // 	      (S.snoc (as_seq h0 blen bv) (B.as_seq h0 v))))
#set-options "--z3rlimit 40"
let insert_copy #a #rg rv v =
  admit ();
  let nrid = new_region_ (V.frameOf rv) in
  let nv = Rgl?.r_create rg nrid in
  Rgl?.r_copy rg v nv;
  insert_ptr rv nv

val assign_ptr:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  i:uint32_t{i < V.size_of rv} -> v:a ->
  HST.ST unit
    (requires (fun h0 ->
      rv_inv h0 rv /\ elem_live rg h0 v /\
      HH.extends (Rgl?.region_of rg v) (V.frameOf rv) /\
      V.forall_all h0 rv
	(fun b -> HH.disjoint (Rgl?.region_of rg b)
			      (Rgl?.region_of rg v))))
    (ensures (fun h0 _ h1 -> 
      modifies (rv_loc_only rv) h0 h1 /\
      rv_inv h1 rv))
      // S.equal (as_seq h1 blen bv)
      // 	      (S.upd (as_seq h0 blen bv) (U32.v i) (B.as_seq h0 v))))
let assign_ptr #a #rg rv i v =
  admit ();
  V.assign rv i v

val assign_copy:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  i:uint32_t{i < V.size_of rv} -> v:a ->
  HST.ST unit
    (requires (fun h0 -> rv_inv h0 rv /\ elem_live rg h0 v))
    (ensures (fun h0 _ h1 -> 
      modifies (loc_region_rg rg (V.get h0 rv i)) h0 h1 /\
      rv_inv h1 rv))
      // S.equal (as_seq h1 blen bv)
      // 	      (S.upd (as_seq h0 blen bv) (U32.v i) (B.as_seq h0 v))))
let assign_copy #a #rg rv i v =
  admit ();
  Rgl?.r_copy rg v (V.index rv i)

val free_elems:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  idx:uint32_t{idx < V.size_of rv} ->
  HST.ST unit
    (requires (fun h0 -> 
      V.live h0 rv /\
      elems_live h0 rv 0ul (idx + 1ul) /\
      rv_disj h0 rv))
    (ensures (fun h0 _ h1 ->
      modifies (rv_loc_elems h0 rv 0 (U32.v idx + 1)) h0 h1))
let rec free_elems #a #rg rv idx =
  admit ();
  Rgl?.r_free rg (V.index rv idx);
  if idx <> 0ul then
    free_elems rv (idx - 1ul)

val free:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  HST.ST unit
    (requires (fun h0 -> rv_inv h0 rv))
    (ensures (fun h0 _ h1 -> modifies (rv_loc_all rv) h0 h1))
let free #a #rg rv =
  admit ();
  (if V.size_of rv = 0ul then () 
  else free_elems rv (V.size_of rv - 1ul));
  V.free rv

