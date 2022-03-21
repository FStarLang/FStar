(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module LowStar.Regional

(**
 * This module defines what is conceptually a typeclass called
 * `regional` (although it is not syntactically marked as a `class`
 * yet).
 *
 * `regional a` is the the class of types whose values have explicit
 * memory allocations confined spatially within a single heap region
 * in the hyperstack memory model.
 *
 * Being confined to a region, values of regional types support a
 * natural framing principles: state mutations that do not overlap
 * with a regional value's region are noninterfering.
 *
 * Instances of regional types are given for buffers and vectors:
 * See LowStar.Regional.Instances, LowStar.RVector for samples.
 *
 *)

open LowStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

/// Regionality

/// Motivation: we want to ensure that all stateful operations for a value of
/// type `a` are within the `region_of` the value.
///
/// Furthermore, we would like regional to be parameterized over another type class
/// that elements can have. However, we are also trying to extract to C, meaning
/// that we can't incur any run-time lookups and indirections. In essence, we'd
/// like for members of a regional to potentially be partial applications where
/// the first argument may be an agility parameter, an extra type class for the
/// elements, etc. etc. except that partial applications are not allowed in C.
///
/// We therefore add an "st" type, which is a piece of (pure) state (hence more
/// like a parameter) that functions are allowed to capture. Currently, only
/// ``r_alloc`` needs that extra parameter. The parameter is stored within the
/// type class, so that clients are not required to manage that piece of state
/// themselves. This is, in effect, closure-conversion for ``r_alloc`` where the
/// closure state is lifted and stored in the regional itself. As such, the only
/// piece of state that ``r_alloc`` may receive is the exact value that was
/// captured.
///
/// Several alternative designs exist, e.g. making ``a`` at type ``st -> Type0``
/// (won't extract); instantiating ``st`` as a singleton type and dropping the
/// refinement (also works, but doesn't make the intent of closure-conversion
/// explicit); dropping the refinement and leaving it up to the user to store
/// the refinement in ``r_inv`` (which would then take ``state`` as an
/// argument)...
noeq type regional (st:Type) (a:Type0) =
| Rgl:
    // This is not really a piece of state, but more like a parameter.
    state: st ->

    // The target type should have a region where it belongs.
    region_of: (a -> GTot HS.rid) ->

    //loc_of for the underlying a
    loc_of: (a -> GTot loc) ->

    // A parameterless value of type `a`.
    // It does not have to satisfy the invariant `r_inv` described below.
    dummy: a ->

    // An invariant we want to maintain for each operation.
    // For example, it may include `live` and `freeable` properties
    // for related objects.
    r_inv: (HS.mem -> a -> GTot Type0) ->
    r_inv_reg:
      (h:HS.mem -> v:a ->
      Lemma (requires (r_inv h v))
            (ensures (HS.live_region h (region_of v)))) ->

    // A representation type of `a` and a corresponding conversion function
    repr: Type0 ->
    r_repr: (h:HS.mem -> v:a{r_inv h v} -> GTot repr) ->

    // A core separation lemma, saying that the invariant and representation are
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
    r_alloc: ((s:st { s == state }) -> r:HST.erid ->
      HST.ST a
        (requires (fun h0 -> True))
        (ensures (fun h0 v h1 ->
          Set.subset (Map.domain (HS.get_hmap h0))
                     (Map.domain (HS.get_hmap h1)) /\
          modifies loc_none h0 h1 /\
          fresh_loc (loc_of v) h0 h1 /\  //the underlying loc is fresh
          r_alloc_p v /\ r_inv h1 v /\ region_of v == r /\
          r_repr h1 v == Ghost.reveal irepr))) ->

    // Destruction: note that it allows to `modify` all the regions, including
    // its subregions. It is fair when we want to `free` a vector and its
    // elements as well, assuming the elements belong to subregions.
    r_free: ((s:st { s == state }) -> v:a ->
      HST.ST unit
        (requires (fun h0 -> r_inv h0 v))
        (ensures (fun h0 _ h1 ->
          modifies (loc_all_regions_from false (region_of v)) h0 h1))) ->

    regional st a

let rg_inv #a #rst (rg: regional rst a) =
  Rgl?.r_inv rg

inline_for_extraction
let rg_dummy #a #rst (rg:regional rst a)
: Tot a
= Rgl?.dummy rg

inline_for_extraction
let rg_alloc #a #rst (rg:regional rst a) (r:HST.erid)
: HST.ST a
  (requires (fun h0 -> True))
  (ensures (fun h0 v h1 ->
           Set.subset (Map.domain (HS.get_hmap h0))
                      (Map.domain (HS.get_hmap h1)) /\
           modifies loc_none h0 h1 /\
           fresh_loc (Rgl?.loc_of rg v) h0 h1 /\
           (Rgl?.r_alloc_p rg) v /\ rg_inv rg h1 v /\ (Rgl?.region_of rg) v == r /\
           (Rgl?.r_repr rg) h1 v == Ghost.reveal (Rgl?.irepr rg)))
= Rgl?.r_alloc rg (Rgl?.state rg) r

inline_for_extraction
let rg_free #a #rst (rg:regional rst a) (v:a)
: HST.ST unit
 (requires (fun h0 -> rg_inv rg h0 v))
 (ensures (fun h0 _ h1 ->
          modifies (loc_all_regions_from false (Rgl?.region_of rg v)) h0 h1))
= (Rgl?.r_free rg) (Rgl?.state rg) v
