module LowStar.Regional

open FStar.All
open FStar.Integers
open FStar.Classical
open LowStar.Modifies

module HH = FStar.Monotonic.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack

/// Regionality

type erid = rid:HH.rid{HST.is_eternal_region rid}

// Motivation: we want to ensure that all stateful operations for a value of
// type `a` are within the `region_of` the value.
noeq type regional a =
| Rgl:
    // The target type should have a region where it belongs.
    region_of: (a -> GTot HH.rid) ->

    // A stateless value of type `a`.
    // It does not have to satisfy the invariant `r_inv` described below.
    dummy: a ->

    // An invariant we want to maintain for each operation.
    // For example, it may include `live` and `freeable` properties
    // for related objects.
    r_inv: (HS.mem -> a -> GTot Type0) ->
    r_inv_reg:
      (h:HS.mem -> v:a ->
      Lemma (requires (r_inv h v))
	    (ensures (MHS.live_region h (region_of v)))) ->

    // A representation type of `a` and a corresponding conversion function
    repr: Type0 ->
    r_repr: (h:HS.mem -> v:a{r_inv h v} -> GTot repr) ->

    // A core separation lemma, saying that the invariant and represenation are
    // preserved when an orthogonal state transition happens.
    r_sep:
      (v:a -> p:loc -> h:HS.mem -> h':HS.mem ->
      Lemma (requires (r_inv h v /\
		      loc_disjoint (loc_all_regions_from false (region_of v)) p /\
		      modifies p h h'))
	    (ensures (r_inv h' v /\ r_repr h v == r_repr h' v))) ->

    /// Allocation
    // The representation for the initial value of type `a`
    irepr: Ghost.erased repr ->

    // A property that should hold for all initial values of type `a`.
    r_alloc_p: (a -> GTot Type0) ->

    // An allocation operation. We might have several ways of initializing a
    // given target type `a`; then multiple typeclass instances should be
    // defined, and each of them can be used properly.
    r_alloc: (r:erid ->
      HST.ST a
	(requires (fun h0 -> True))
	(ensures (fun h0 v h1 ->
	  Set.subset (Map.domain (HS.get_hmap h0))
	  	     (Map.domain (HS.get_hmap h1)) /\
	  modifies loc_none h0 h1 /\ 
	  r_alloc_p v /\ r_inv h1 v /\ region_of v == r /\
	  r_repr h1 v == Ghost.reveal irepr))) ->

    // Destruction: note that it allows to `modify` all the regions, including
    // its subregions. It is fair when we want to `free` a vector and its 
    // elements as well, assuming the elements belong to subregions.
    r_free: (v:a ->
      HST.ST unit
	(requires (fun h0 -> r_inv h0 v))
	(ensures (fun h0 _ h1 ->
	  modifies (loc_all_regions_from false (region_of v)) h0 h1))) ->
    regional a

