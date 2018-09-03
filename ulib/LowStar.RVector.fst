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
    irepr: Ghost.erased repr ->
    r_init: (r:erid ->
      HST.ST a
	(requires (fun h0 -> true))
	(ensures (fun h0 v h1 -> 
	  modifies loc_none h0 h1 /\ r_inv h1 v /\
	  region_of v = r /\ MHS.fresh_region r h0 h1 /\
	  r_repr h1 v == Ghost.reveal irepr))) ->

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

/// The invariant of rvector

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

/// Fine-grained control of regions (frames)

private val rv_loc_elem:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t{i < V.size_of rv} ->
  GTot loc
private let rv_loc_elem #a #rg h rv i =
  B.loc_all_regions_from false 
    (Rgl?.region_of rg (S.index (V.as_seq h rv) (U32.v i)))

private val rv_loc_elems:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} -> 
  GTot loc (decreases (U32.v j))
private let rec rv_loc_elems #a #rg h rv i j =
  if i = j then loc_none
  else loc_union (rv_loc_elems h rv i (j - 1ul))
		 (rv_loc_elem h rv (j - 1ul))

// Inclusion

val loc_all_exts_from: 
  preserve_liveness: bool -> r: HH.rid -> GTot loc
let loc_all_exts_from preserve_liveness r =
  B.loc_regions 
    preserve_liveness
    (Set.intersect
      (HS.mod_set (Set.singleton r))
      (Set.complement (Set.singleton r)))

private val rv_loc_elem_included:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t{i < V.size_of rv} ->
  Lemma (requires (HH.extends (Rgl?.region_of rg (V.get h rv i))
			      (V.frameOf rv)))
	(ensures (loc_includes (loc_all_exts_from false (V.frameOf rv))
  			       (rv_loc_elem h rv i)))
private let rv_loc_elem_included #a #rg h rv i = ()

private val rv_loc_elems_included:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} -> 
  Lemma (requires (elems_reg h rv i j))
	(ensures (loc_includes (loc_all_exts_from false (V.frameOf rv))
  			       (rv_loc_elems h rv i j)))
	(decreases (U32.v j))
private let rec rv_loc_elems_included #a #rg h rv i j =
  if i = j then ()
  else (rv_loc_elem_included h rv (j - 1ul);
       rv_loc_elems_included h rv i (j - 1ul))

// Disjointness

private val rv_loc_elem_disj:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} -> 
  k:uint32_t{i <= k && k < j} ->
  l:uint32_t{i <= l && l < j && k <> l} ->
  Lemma (requires (elems_reg h rv i j))
	(ensures (loc_disjoint (rv_loc_elem h rv k)
			       (rv_loc_elem h rv l)))
private let rv_loc_elem_disj #a #rg h rv i j k l =
  V.forall2_seq_ok
    (V.as_seq h rv) (U32.v i) (U32.v j) (U32.v k) (U32.v l)
    (fun v1 v2 -> HH.disjoint (Rgl?.region_of rg v1)
  			      (Rgl?.region_of rg v2))

private val rv_loc_elems_elem_disj:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} -> 
  k1:uint32_t{i <= k1} ->
  k2:uint32_t{k1 <= k2 && k2 < j} ->
  l:uint32_t{i <= l && l < j && (l < k1 || k2 <= l)} ->
  Lemma (requires (elems_reg h rv i j))
	(ensures (loc_disjoint (rv_loc_elems h rv k1 k2)
			       (rv_loc_elem h rv l)))
	(decreases (U32.v k2))
private let rec rv_loc_elems_elem_disj #a #rg h rv i j k1 k2 l =
  if k1 = k2 then ()
  else (rv_loc_elem_disj h rv i j (k2 - 1ul) l;
       rv_loc_elems_elem_disj h rv i j k1 (k2 - 1ul) l)

private val rv_loc_elems_disj:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} -> 
  k1:uint32_t{i <= k1} ->
  k2:uint32_t{k1 <= k2 && k2 < j} ->
  l1:uint32_t{i <= l1} ->
  l2:uint32_t{l1 <= l2 && l2 < j} ->
  Lemma (requires (elems_reg h rv i j /\ (k2 <= l1 || l2 <= k1)))
	(ensures (loc_disjoint (rv_loc_elems h rv k1 k2)
			       (rv_loc_elems h rv l1 l2)))
	(decreases (U32.v k2))
private let rec rv_loc_elems_disj #a #rg h rv i j k1 k2 l1 l2 =
  if k1 = k2 then ()
  else (rv_loc_elems_elem_disj h rv i j l1 l2 (k2 - 1ul);
       rv_loc_elems_disj h rv i j k1 (k2 - 1ul) l1 l2)

// Preservation based on disjointness

private val rv_loc_elem_preserved:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  i:uint32_t{i < V.size_of rv} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (loc_disjoint p (V.loc_vector_within rv i (i + 1ul)) /\
		  modifies p h0 h1))
	(ensures (rv_loc_elem h0 rv i == rv_loc_elem h1 rv i))
private let rv_loc_elem_preserved #a #rg rv i p h0 h1 =
  // Requires a more general version of `V.get_preserved`
  assume (V.get h0 rv i == V.get h1 rv i)

private val rv_loc_elems_preserved:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  i:uint32_t -> j:uint32_t{i <= j && j < V.size_of rv} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (loc_disjoint p (V.loc_vector_within rv i j) /\
		  modifies p h0 h1))
	(ensures (rv_loc_elems h0 rv i j ==
		 rv_loc_elems h1 rv i j))
	(decreases (U32.v j))
private let rec rv_loc_elems_preserved #a #rg rv i j p h0 h1 =
  if i = j then ()
  else (rv_loc_elem_preserved rv (j - 1ul) p h0 h1;
       rv_loc_elems_preserved rv i (j - 1ul) p h0 h1)

private val elem_inv_preserved:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  i:uint32_t{i < V.size_of rv} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (Rgl?.r_inv rg h0 (V.get h0 rv i) /\
		  loc_disjoint p (V.loc_vector_within rv i (i + 1ul)) /\
		  loc_disjoint p (rv_loc_elem h0 rv i) /\
		  modifies p h0 h1))
	(ensures (Rgl?.r_inv rg h1 (V.get h1 rv i)))
private let elem_inv_preserved #a #rg rv i p h0 h1 =
  // Requires a more general version of `V.get_preserved`
  assume (V.get h0 rv i == V.get h1 rv i);
  Rgl?.r_sep rg (V.get h0 rv i) p h0 h1

private val elems_inv_preserved:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (elems_inv h0 rv i j /\
		  loc_disjoint p (V.loc_vector_within rv i j) /\
		  loc_disjoint p (rv_loc_elems h0 rv i j) /\
		  modifies p h0 h1))
	(ensures (elems_inv h1 rv i j))
	(decreases (U32.v j))
private let rec elems_inv_preserved #a #rg rv i j p h0 h1 =
  if i = j then ()
  else (elems_inv_preserved rv i (j - 1ul) p h0 h1;
       elem_inv_preserved rv (j - 1ul) p h0 h1)

/// Representation

val as_seq_seq:
  #a:Type0 -> #rg:regional a -> 
  h:HS.mem -> rs:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length rs} ->
  GTot (s:S.seq (Rgl?.repr rg){S.length s = j - i})
       (decreases j)
let rec as_seq_seq #a #rg h rs i j =
  if i = j then S.empty
  else S.snoc (as_seq_seq h rs i (j - 1))
	      (Rgl?.r_repr rg h (S.index rs (j - 1)))

val as_seq_sub:
  #a:Type0 -> #rg:regional a -> 
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} ->
  GTot (s:S.seq (Rgl?.repr rg){S.length s = U32.v j - U32.v i})
       (decreases (U32.v j))
let rec as_seq_sub #a #rg h rv i j =
  as_seq_seq h (V.as_seq h rv) (U32.v i) (U32.v j)

val as_seq:
  #a:Type0 -> #rg:regional a -> 
  h:HS.mem -> rv:rvector rg ->
  GTot (s:S.seq (Rgl?.repr rg){S.length s = U32.v (V.size_of rv)})
let rec as_seq #a #rg h rv =
  as_seq_sub h rv 0ul (V.size_of rv)

val as_seq_sub_as_seq:
  #a:Type0 -> #rg:regional a -> 
  h:HS.mem -> rv:rvector rg ->
  Lemma (S.equal (as_seq_sub h rv 0ul (V.size_of rv))
		 (as_seq h rv))
	[SMTPat (as_seq_sub h rv 0ul (V.size_of rv))]
let as_seq_sub_as_seq #a #rg h rv = ()

val as_seq_seq_upd:
  #a:Type0 -> #rg:regional a -> 
  h:HS.mem -> rs:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length rs} ->
  k:nat{i <= k && k < j} -> v:a ->
  Lemma (S.equal (as_seq_seq h (S.upd rs k v) i j)
		 (S.upd (as_seq_seq h rs i j) (k - i) (Rgl?.r_repr rg h v)))
let as_seq_seq_upd #a #rg h rs i j k v =
  admit ()

// Preservation based on disjointness

// val as_seq_seq_preserved:
//   #a:Type0 -> #rg:regional a -> 
//   h:HS.mem -> rs:S.seq a ->
//   i:nat -> j:nat{i <= j && j <= S.length rs} ->
//   p:loc -> h0:HS.mem -> h1:HS.mem ->
//   Lemma (requires (rv_loc_elems
  // loc_disjoint p (loc_all_exts_from
  // 		  modifies p h0 h1))
  // 	(ensures (rv_loc_elem h0 rv i == rv_loc_elem h1 rv i))
  

// val vec_as_seq_eq_rv_inv:
//   #a:Type0 -> #rg:regional a -> 
//   h1:HS.mem -> h2:HS.mem ->
//   rv1:rvector rg -> rv2:rvector rg ->
//   Lemma (requires (rv_inv h1 rv1 /\
// 		  S.equal (V.as_seq h1 rv1) (V.as_seq h2 rv2)))
// 	(ensures (rv_inv h2 rv2))
// let vec_as_seq_eq_rv_inv #a #rg h1 h2 rv1 rv2 =
//   admit ()

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
      elems_reg h1 rv 0ul cidx /\
      S.equal (as_seq_sub h1 rv 0ul cidx)
      	      (S.create (U32.v cidx) (Ghost.reveal (Rgl?.irepr rg))) /\
      // the loop invariant for this function
      V.forall_ h1 rv 0ul cidx
	(fun r -> MHS.fresh_region (Rgl?.region_of rg r) h0 h1)))
    (decreases (U32.v cidx))
private let rec create_ #a #rg rv cidx =
  if cidx = 0ul then ()
  else (let nrid = new_region_ (V.frameOf rv) in
       let r_init = Rgl?.r_init rg in
       let v = r_init nrid in

       let hh1 = HST.get () in
       V.assign rv (cidx - 1ul) v;

       let hh2 = HST.get () in
       Rgl?.r_sep
	 rg (V.get hh2 rv (cidx - 1ul))
	 (V.loc_vector_within rv (cidx - 1ul) cidx)
	 hh1 hh2;
       create_ rv (cidx - 1ul);

       let hh3 = HST.get () in
       Rgl?.r_sep
	 rg (V.get hh3 rv (cidx - 1ul))
	 (V.loc_vector_within rv 0ul (cidx - 1ul))
	 hh2 hh3;
       elem_inv_preserved 
       	 rv (cidx - 1ul) (V.loc_vector_within rv 0ul (cidx - 1ul))
       	 hh2 hh3;
       V.forall2_extend hh3 rv 0ul (cidx - 1ul)
	 (fun r1 r2 -> HH.disjoint (Rgl?.region_of rg r1)
				   (Rgl?.region_of rg r2)))

val create_rid:
  #a:Type0 -> rg:regional a ->
  len:uint32_t{len > 0ul} -> rid:erid ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 rv h1 ->
      modifies (V.loc_vector rv) h0 h1 /\
      rv_inv h1 rv /\
      V.frameOf rv = rid /\
      V.size_of rv = len /\
      S.equal (as_seq h1 rv) 
	      (S.create (U32.v len) (Ghost.reveal (Rgl?.irepr rg)))))
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
      V.size_of rv = 0ul /\
      S.equal (as_seq h1 rv) S.empty))
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
      V.size_of rv = len /\
      S.equal (as_seq h1 rv)
      	      (S.create (U32.v len) (Ghost.reveal (Rgl?.irepr rg)))))
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
      modifies (loc_union (V.loc_addr_of_vector rv)
			  (V.loc_vector irv)) h0 h1 /\
      rv_inv h1 irv /\
      S.equal (as_seq h1 irv)
      	      (S.snoc (as_seq h0 rv) (Rgl?.r_repr rg h0 v))))
let insert #a #rg rv v =
  let hh0 = HST.get () in
  let irv = V.insert rv v in
  let hh1 = HST.get () in

  assert (V.frameOf rv = V.frameOf irv);
  assert (modifies (loc_union (V.loc_addr_of_vector rv)
			      (V.loc_vector irv)) hh0 hh1);

  Rgl?.r_sep rg v
    (loc_union (V.loc_addr_of_vector rv) (V.loc_vector irv))
    hh0 hh1;
  assert (Rgl?.r_repr rg hh0 v == Rgl?.r_repr rg hh1 v);
  assert (Rgl?.r_inv rg hh1 v);

  assert (S.equal (V.as_seq hh0 rv)
		  (S.slice (V.as_seq hh1 irv) 0 (U32.v (V.size_of rv))));
  // vec_as_seq_eq_rv_inv 
  //   hh0 hh1 (V.as_seq hh0 rv) 
  //   (S.slice (V.as_seq hh1 irv) 0 (U32.v (V.size_of rv)));

  // assert (rv_inv #a #rg hh1 irv);
  // assert (S.equal (as_seq hh1 irv)
  //     		  (S.snoc (as_seq hh0 rv) (Rgl?.r_repr rg hh0 v)));

  admit () // irv

val insert_copy:
  #a:Type0 -> #rg:regional a -> cp:copyable a rg ->
  rv:rvector rg{not (V.is_full rv)} -> v:a ->
  HST.ST (rvector rg)
    (requires (fun h0 -> 
      rv_inv h0 rv /\ Rgl?.r_inv rg h0 v))
    (ensures (fun h0 irv h1 ->
      V.frameOf rv = V.frameOf irv /\
      modifies (loc_all_regions_from false (V.frameOf rv)) h0 h1 /\
      rv_inv h1 irv /\
      S.equal (as_seq h1 irv)
      	      (S.snoc (as_seq h0 rv) (Rgl?.r_repr rg h0 v))))
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
      rv_inv h1 rv /\
      S.equal (as_seq h1 rv)
      	      (S.upd (as_seq h0 rv) (U32.v i) (Rgl?.r_repr rg h0 v))))
#reset-options "--z3rlimit 10"
let assign #a #rg rv i v =
  let hh0 = HST.get () in
  V.assign rv i v;

  let hh1 = HST.get () in
  rv_loc_elems_included hh0 rv 0ul i;
  rv_loc_elems_included hh0 rv (i + 1ul) (V.size_of rv);

  // `rv_inv` is preserved
  // elems_inv_preserved
  //   rv 0ul i (V.loc_vector_within rv i (i + 1ul)) hh0 hh1;
  // elems_inv_preserved
  //   rv (i + 1ul) (V.size_of rv) (V.loc_vector_within rv i (i + 1ul)) hh0 hh1;
  Rgl?.r_sep rg (V.get hh1 rv i) (V.loc_vector_within rv i (i + 1ul)) hh0 hh1;
  // assert (rv_inv hh1 rv);

  // TODO: correctness

  assert (S.equal (V.as_seq hh1 rv)
		  (S.upd (V.as_seq hh0 rv) (U32.v i) v));
  assert (S.equal (as_seq hh1 rv)
		  (as_seq_seq hh1 (S.upd (V.as_seq hh0 rv) (U32.v i) v)
			      0 (U32.v (V.size_of rv))));
  as_seq_seq_upd #a #rg
    hh1 (V.as_seq hh0 rv) 0 (U32.v (V.size_of rv))
    (U32.v i) v;
  assert (S.equal (as_seq hh1 rv)
  		  (S.upd (as_seq_seq hh1 (V.as_seq hh0 rv)
  				     0 (U32.v (V.size_of rv)))
  			 (U32.v i) (Rgl?.r_repr rg hh0 v)));
  admit ()

val assign_copy:
  #a:Type0 -> #rg:regional a -> cp:copyable a rg ->
  rv:rvector rg -> 
  i:uint32_t{i < V.size_of rv} -> v:a ->
  HST.ST unit
    (requires (fun h0 -> rv_inv h0 rv /\ Rgl?.r_inv rg h0 v))
    (ensures (fun h0 _ h1 -> 
      modifies (loc_region_only 
	         false (Rgl?.region_of rg (V.get h0 rv i))) h0 h1 /\
      rv_inv h1 rv /\
      S.equal (as_seq h1 rv)
      	      (S.upd (as_seq h0 rv) (U32.v i) (Rgl?.r_repr rg h0 v))))
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
      modifies (rv_loc_elems h0 rv 0ul (idx + 1ul)) h0 h1))
let rec free_elems #a #rg rv idx =
  let hh0 = HST.get () in
  let r_free = Rgl?.r_free rg in
  r_free (V.index rv idx);

  let hh1 = HST.get () in
  rv_loc_elems_elem_disj hh0 rv 0ul (idx + 1ul) 0ul idx idx;
  elems_inv_preserved 
    rv 0ul idx (rv_loc_elem hh0 rv idx) hh0 hh1;
  rv_loc_elems_preserved
    rv 0ul idx (rv_loc_elem hh0 rv idx) hh0 hh1;

  if idx <> 0ul then
    free_elems rv (idx - 1ul)

val free:
  #a:Type0 -> #rg:regional a -> rv:rvector rg -> 
  HST.ST unit
    (requires (fun h0 -> rv_inv h0 rv))
    (ensures (fun h0 _ h1 -> 
      modifies (loc_all_regions_from false (V.frameOf rv)) h0 h1))
let free #a #rg rv =
  let hh0 = HST.get () in
  (if V.size_of rv = 0ul then () 
  else free_elems rv (V.size_of rv - 1ul));
  let hh1 = HST.get () in
  rv_loc_elems_included hh0 rv 0ul (V.size_of rv);
  V.free rv

