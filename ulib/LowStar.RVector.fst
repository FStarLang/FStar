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

// `HST.new_region` does not guarantee `modifies loc_none h0 h1`, which is
// a bit annoying. It can be proven by `B.modifies_none_modifies` and here
// `new_region_` is exactly doing that.
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

// Motivation: we want to ensure that all stateful operations for a value of
// type `a` are within the `region_of` the value.
noeq type regional a =
| Rgl:
    region_of: (a -> GTot HH.rid) ->

    // A non-stateful chosen value of type `a`.
    // Note that the value doesn't need to satisfy the stateful invariant.
    cv: a ->

    // A representation type of `a` and a corresponding conversion function
    repr: Type0 ->
    r_repr: (HS.mem -> a -> GTot repr) ->

    // An invariant we want to maintain for each operation.
    // For example, it may include `live` and `freeable` properties
    // for related objects.
    r_inv: (HS.mem -> a -> GTot Type0) ->

    // A core separation lemma, saying that the invariant and represenation
    // are preserved when an orthogonal state transition happens.
    r_sep:
      (v:a -> p:loc -> h:HS.mem -> h':HS.mem ->
      Lemma (requires (r_inv h v /\
		      loc_disjoint 
			(loc_all_regions_from false (region_of v)) p /\
		      modifies p h h'))
	    (ensures (r_inv h' v /\ r_repr h v == r_repr h' v))) ->

    // Construction
    r_init: (r:erid ->
      HST.ST a
	(requires (fun h0 -> true))
	(ensures (fun h0 v h1 -> 
	  modifies loc_none h0 h1 /\ r_inv h1 v /\ region_of v = r))) ->

    // Destruction
    r_free: (v:a ->
      HST.ST unit
	(requires (fun h0 -> r_inv h0 v))
	(ensures (fun h0 _ h1 ->
	  modifies (loc_all_regions_from false (region_of v)) h0 h1))) ->
    regional a

// A regional type `a` is also `copyable` when there exists a copy operator
// that guarantees the same representation between `src` and `dst`.
// For example, the `copy` operation for `B.buffer a` is `B.blit`.
noeq type copyable a (rg: regional a) =
| Cpy:
    copy: (src:a -> dst:a ->
      HST.ST unit
    	(requires (fun h0 ->
    	  Rgl?.r_inv rg h0 src /\ Rgl?.r_inv rg h0 dst /\
    	  HH.disjoint (Rgl?.region_of rg src)
		      (Rgl?.region_of rg dst)))
    	(ensures (fun h0 _ h1 ->
    	  modifies (loc_all_regions_from 
		     false (Rgl?.region_of rg dst)) h0 h1 /\
    	  Rgl?.r_inv rg h1 dst /\
    	  Rgl?.r_repr rg h1 dst == Rgl?.r_repr rg h0 src))) ->
    copyable a rg

type rvector #a (rg:regional a) = V.vector a

/// The invariant for each element

val elems_inv:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg -> 
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} ->
  GTot Type0
let elems_inv #a #rg h rv i j =
  V.forall_ h rv i j (Rgl?.r_inv rg h)

val rv_elems_inv:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg -> GTot Type0
let rv_elems_inv #a #rg h rv =
  elems_inv h rv 0ul (V.size_of rv)

val elems_reg:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} ->
  GTot Type0
let elems_reg #a #rg h rv i j =
  V.forall_ h rv i j
    (fun v -> HH.extends (Rgl?.region_of rg v) (V.frameOf rv)) /\
  V.forall2 h rv i j
    (fun v1 v2 -> HH.disjoint (Rgl?.region_of rg v1)
			      (Rgl?.region_of rg v2))

val rv_elems_reg:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg -> GTot Type0
let rv_elems_reg #a #rg h rv =
  elems_reg h rv 0ul (V.size_of rv)

// The invariant of rvector

val rv_itself_inv:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg -> GTot Type0
let rv_itself_inv #a #rg h rv =
  V.live h rv /\ V.freeable rv /\
  HST.is_eternal_region (V.frameOf rv)

val rv_inv:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg -> GTot Type0
let rv_inv #a #rg h rv =
  rv_elems_inv h rv /\
  rv_elems_reg h rv /\
  rv_itself_inv h rv

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
  #a:Type0 -> rg:regional a ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 bv h1 -> h0 == h1 /\ V.size_of bv = 0ul))
let create_empty #a rg =
  V.create_empty a

private val create_:
  #a:Type0 -> #rg:regional a -> rv:rvector rg ->
  cidx:uint32_t{cidx <= V.size_of rv} -> 
  HST.ST unit
    (requires (fun h0 -> rv_itself_inv h0 rv))
    (ensures (fun h0 _ h1 ->
      modifies (V.loc_vector_within rv 0ul cidx) h0 h1 /\
      rv_itself_inv h1 rv /\
      elems_inv h1 rv 0ul cidx /\
      elems_reg h1 rv 0ul cidx))
    (decreases (U32.v cidx))
private let rec create_ #a #rg rv cidx =
  admit ();
  if cidx = 0ul then ()
  else (let hh0 = HST.get () in
       let nrid = new_region_ (V.frameOf rv) in
       let r_init = Rgl?.r_init rg in
       let v = r_init nrid in
       V.assign rv (cidx - 1ul) v;
       create_ rv (cidx - 1ul))

val create_rid:
  #a:Type0 -> rg:regional a ->
  len:uint32_t{len > 0ul} -> rid:erid ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 rv h1 ->
      modifies (V.loc_vector rv) h0 h1 /\
      rv_inv h1 rv /\
      V.frameOf rv = rid /\
      V.size_of rv = len))
      // S.equal (as_seq h1 blen bv) 
      // 	      (S.create (U32.v len) (S.create (U32.v blen) ia))))
let create_rid #a rg len rid =
  let vec = V.create_rid len (Rgl?.cv rg) rid in
  create_ #a #rg vec len;
  vec

val create_reserve:
  #a:Type0 -> rg:regional a ->
  len:uint32_t{len > 0ul} -> rid:erid ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 rv h1 ->
      modifies (V.loc_vector rv) h0 h1 /\
      rv_inv h1 rv /\
      V.frameOf rv = rid /\
      V.size_of rv = 0ul))
      // S.equal (as_seq h1 blen bv) S.empty))
let create_reserve #a rg len rid =
  V.create_reserve len (Rgl?.cv rg) rid

val create:
  #a:Type0 -> rg:regional a ->
  len:uint32_t{len > 0ul} ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 rv h1 ->
      modifies (V.loc_vector rv) h0 h1 /\
      rv_inv h1 rv /\
      MHS.fresh_region (V.frameOf rv) h0 h1 /\
      V.size_of rv = len))
      // S.equal (as_seq h1 blen bv)
      // 	      (S.create (U32.v len) (S.create (U32.v blen) ia))))
let create #a rg len =
  let nrid = new_region_ HH.root in
  create_rid rg len nrid

val insert:
  #a:Type0 -> #rg:regional a ->
  rv:rvector rg{not (V.is_full rv)} -> v:a ->
  HST.ST (rvector rg)
    (requires (fun h0 ->
      rv_inv h0 rv /\ Rgl?.r_inv rg h0 v /\
      HH.extends (Rgl?.region_of rg v) (V.frameOf rv) /\
      V.forall_all h0 rv
	(fun b -> HH.disjoint (Rgl?.region_of rg b)
			      (Rgl?.region_of rg v))))
    (ensures (fun h0 irv h1 ->
      V.frameOf rv = V.frameOf irv /\
      modifies (V.loc_vector rv) h0 h1 /\
      rv_inv h1 irv))
      // S.equal (as_seq h1 blen ibv)
      // 	      (S.snoc (as_seq h0 blen bv) (B.as_seq h0 v))))
let insert #a #rg rv v =
  admit ();
  V.insert rv v

val insert_copy:
  #a:Type0 -> #rg:regional a -> cp:copyable a rg ->
  rv:rvector rg{not (V.is_full rv)} -> v:a ->
  HST.ST (rvector rg)
    (requires (fun h0 -> 
      rv_inv h0 rv /\ Rgl?.r_inv rg h0 v))
    (ensures (fun h0 irv h1 ->
      V.frameOf rv = V.frameOf irv /\
      modifies (loc_all_regions_from false (V.frameOf rv)) h0 h1 /\
      rv_inv h1 irv))
      // S.equal (as_seq h1 blen ibv)
      // 	      (S.snoc (as_seq h0 blen bv) (B.as_seq h0 v))))
let insert_copy #a #rg cp rv v =
  admit ();
  let nrid = new_region_ (V.frameOf rv) in
  let r_init = Rgl?.r_init rg in
  let nv = r_init nrid in
  let copy = Cpy?.copy cp in
  copy v nv;
  insert rv nv

val assign:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  i:uint32_t{i < V.size_of rv} -> v:a ->
  HST.ST unit
    (requires (fun h0 ->
      rv_inv h0 rv /\ Rgl?.r_inv rg h0 v /\
      HH.extends (Rgl?.region_of rg v) (V.frameOf rv) /\
      V.forall_all h0 rv
	(fun b -> HH.disjoint (Rgl?.region_of rg b)
			      (Rgl?.region_of rg v))))
    (ensures (fun h0 _ h1 -> 
      modifies (V.loc_vector rv) h0 h1 /\
      rv_inv h1 rv))
      // S.equal (as_seq h1 blen bv)
      // 	      (S.upd (as_seq h0 blen bv) (U32.v i) (B.as_seq h0 v))))
let assign #a #rg rv i v =
  admit ();
  V.assign rv i v

val assign_copy:
  #a:Type0 -> #rg:regional a -> cp:copyable a rg ->
  rv:rvector rg -> 
  i:uint32_t{i < V.size_of rv} -> v:a ->
  HST.ST unit
    (requires (fun h0 -> rv_inv h0 rv /\ Rgl?.r_inv rg h0 v))
    (ensures (fun h0 _ h1 -> 
      modifies (loc_region_only 
	         false (Rgl?.region_of rg (V.get h0 rv i))) h0 h1 /\
      rv_inv h1 rv))
      // S.equal (as_seq h1 blen bv)
      // 	      (S.upd (as_seq h0 blen bv) (U32.v i) (B.as_seq h0 v))))
let assign_copy #a #rg cp rv i v =
  admit ();
  let copy = Cpy?.copy cp in
  copy v (V.index rv i)

val free_elems:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  idx:uint32_t{idx < V.size_of rv} ->
  HST.ST unit
    (requires (fun h0 -> 
      V.live h0 rv /\
      elems_inv h0 rv 0ul (idx + 1ul) /\
      elems_reg h0 rv 0ul (idx + 1ul)))
    (ensures (fun h0 _ h1 ->
      modifies (rv_loc_elems h0 rv 0 (U32.v idx + 1)) h0 h1))
let rec free_elems #a #rg rv idx =
  admit ();
  let r_free = Rgl?.r_free rg in
  r_free (V.index rv idx);
  if idx <> 0ul then
    free_elems rv (idx - 1ul)

val free:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  HST.ST unit
    (requires (fun h0 -> rv_inv h0 rv))
    (ensures (fun h0 _ h1 -> 
      modifies (loc_all_regions_from false (V.frameOf rv)) h0 h1))
let free #a #rg rv =
  admit ();
  (if V.size_of rv = 0ul then () 
  else free_elems rv (V.size_of rv - 1ul));
  V.free rv

