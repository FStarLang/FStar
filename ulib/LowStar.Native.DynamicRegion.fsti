(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.Native.DynamicRegion
open FStar.Preorder
module U32 = FStar.UInt32
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

/// A dynamic region is a refinement of the regions defined in
/// FStar.HyperStack (HS). Wheres HS regions are a purely static
/// concept (they serve only to group related stack or heap references
/// into an abstract footprint), dynamic regions allow concretely
/// allocating heap references within a single abstract store and for
/// that store to be reclaimed in bulk with a single operation to free
/// the entire region.
///
/// This is beneficial for two reasons:
///
///  - The liveness of a references can be bound to the liveness of
///    the region, so a client need only maintain the liveness of the
///    region as an invariant, rather than the liveness of several
///    (potentially unbounded) references.q
///
///  - This simplifies their concrete memory reclamation strategy and
///    helps eliminate memory leaks
///
/// Not all references in a dynamic region need to be reclaimed in
/// bulk. Some of them can be reclaimed early---for these, there is
/// little additional benefit provided by this module over
/// HS.rid. Still, we support such references for uniformity---a
/// client can allocate a single drgn for both kinds of references,
/// rather than needing to allocate a separate rid for short-lived
/// allocations. In the future, the runtime support for this library
/// will also support reclaiming when the region is freed all
/// short-lived references that have not yet been explicitly
/// freed. However, for now, any such short-lived reference must be
/// free explicitly to avoid a memory leak.
///
/// In addition to references, this module supports allocating and
/// freeing buffers within dynamic regions, again in two varieties:
/// region lifetime and early frees.
///
/// Dynamic regions resemble constructs in other languages, notably
/// support for Berger et al.'s "reaps" in Cyclone
///
///   https://people.cs.umass.edu/~emery/pubs/berger-oopsla2002.pdf
///   http://www.cs.umd.edu/projects/PL/cyclone/scp.pdf


/// We distinguish heap regions from stack regions
/// Dynamic regions are for the heap only
let is_heap_region (r:HS.rid) : GTot bool =
  HS.is_eternal_color (HS.color r) //we should rename HS.is_eternal_region to HS.is_heap_region

/// All eternal regions are heap_regions
let eternal_heap_regions (r:HS.rid)
  : Lemma (HST.is_eternal_region r ==> is_heap_region r)
  = ()

/// The type of heap regions
let h_rid = r:HS.rid { is_heap_region r }

/// A wrapper around a library function to create a new heap region
let new_heap_region (m:HS.mem)
                    (parent:h_rid{HS.live_region m parent})
  : Tot (t:(h_rid * HS.mem){HS.fresh_region (fst t) m (snd t)})
  = let rid, m = HS.new_eternal_region m parent None in
    rid, m

/// At runtime, this is extracted to the `handle`
/// type from LowStar.RegionAllocator
val drgn : Type0

/// The model provides a way to project a classic "static"
/// heap region identifier from a drgn
val rid_of_drgn: drgn -> Tot h_rid

/// Allocates a fresh dynamic region within parent
/// Spec is similar to ST.new_region
/// Extracted to `new_handle`
val new_drgn (parent:HST.erid)
  : HST.ST drgn
    (requires fun m        -> True)
    (ensures  fun m0 d m1 ->
      let r0 = parent in
      let r1 = rid_of_drgn d in
      let open HS in
      r1 `extends` r0 /\
      fresh_region r1 m0 m1 /\
      color r1 = color r0 /\
      get_hmap m1 == Map.upd (get_hmap m0) r1 Heap.emp /\
      get_tip m1 == get_tip m0 /\
      live_region m0 r0 /\
      (r1, m1) == new_heap_region m0 r0)

/// Deallocates the region and all its contained objects
/// (Similar in spirit to pop_frame)
/// Exracted to `free_handle`
val free_drgn (d:drgn)
  : HST.ST unit
    (requires fun h ->
      HS.live_region h (rid_of_drgn d))
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_region_only false (rid_of_drgn d)) h0 h1)

(*** Allocating and Free'ing references ***)

/// We support allocating two kinds of references in a dynamic region:
///
///   -- region-lifetime refs are live so long as their enclosing
///      region is live. They are reclaimed only when the entire
///      region is reclaimed
///
///   -- short-lived refs are associated with the region, but they can
///      be allocated and freed manually


/// This is an abstract predicate recording that `r`'s lifetime is
/// bound to the lifetime of `d`
val region_lifetime_ref (#a:Type) (#rel:preorder a) (d:drgn) (r:HST.mref a rel) : prop

/// Eliminating the abstract predicate via a stateful lemma, i.e., a "recall"
val recall_liveness_ref (#a:Type) (#rel:preorder a) (d:drgn) (r:HST.mref a rel)
  : HST.ST unit
    (requires fun h ->
      region_lifetime_ref d r /\
      HS.live_region h (rid_of_drgn d))
    (ensures fun h0 _ h1 ->
      h0 == h1 /\
      h1 `HS.contains` r)

/// Allocate a "region-lifetime" reference to `init` in
/// within `d`. The returned reference is live so long as `d` is
/// Extracted to `a *p = (a)RegionAllocator.alloc d (sizeof a); *p = init;`
val ralloc (#a:Type) (#rel:preorder a) (d:drgn) (init:a)
  : HST.ST (HST.mref a rel)
    (requires fun h ->
      HS.live_region h (rid_of_drgn d))
    (ensures fun h0 r h1 ->
      HST.ralloc_post (rid_of_drgn d) init h0 r h1 /\
      region_lifetime_ref d r)

/// Allocate a manually-managed reference to `init` within `d`.
/// Extracted as just a normal `malloc` (not allocated concretely in d)
///
/// Note: this could almost be implemented directly using HST.ralloc_mm
///
/// However, that function is specialized to work only on HST.is_eternal_region
/// That restriction should be relaxed
val ralloc_mm (#a:Type) (#rel:preorder a) (d:drgn) (init:a)
  : HST.ST (HST.mmmref a rel)
    (requires fun h ->
      HS.live_region h (rid_of_drgn d))
    (ensures fun h0 r h1 ->
      HST.ralloc_post (rid_of_drgn d) init h0 r h1)

/// Free a manually-managed reference
/// Extracted as just an normal `free` (since r is not allocated concretely in d)
inline_for_extraction
let rfree (#a:Type) (#rel:preorder a) (r:HST.mmmref a rel)
  : HST.ST unit
    (requires fun h ->
      h `HS.contains` r)
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_freed_mreference r) h0 h1)
  = HST.rfree r

(*** Allocating and Free'ing buffers ***)

/// This is an abstract predicate recording that the buffer `b`'s lifetime is
/// bound to the lifetime of `d`
val region_lifetime_buf (#a:Type) (#rrel #rel:B.srel a) (d:drgn) (b:B.mbuffer a rrel rel) : prop

/// Eliminating the abstract predicate via a stateful lemma, i.e., a "recall"
val recall_liveness_buf (#a:Type) (#rrel #rel:B.srel a) (d:drgn) (b:B.mbuffer a rrel rel)
  : HST.ST unit
    (requires fun h ->
      region_lifetime_buf d b /\
      HS.live_region h (rid_of_drgn d))
    (ensures fun h0 _ h1 ->
      h0 == h1 /\
      h1 `B.live` b)

/// Allocating a region-lifetime buffer
val ralloc_buf (#a:Type0) (#rrel:B.srel a) (r:drgn) (init:a) (len:U32.t)
  : HST.ST (B.lmbuffer a rrel rrel (U32.v len))
    (requires fun h ->
      U32.v len > 0 /\
      HS.live_region h (rid_of_drgn r))
    (ensures fun h0 b h1 ->
      B.alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init) /\
      B.frameOf b == rid_of_drgn r /\
      region_lifetime_buf r b)

/// Allocating a region-lifetime buffer, initializing its contents
/// with another buffer
val ralloc_and_blit_buf (#a:Type0) (#rrel:B.srel a) (r:drgn)
  (#rrel1 #rel1:_) (src:B.mbuffer a rrel1 rel1) (from len:U32.t)
  : HST.ST (B.lmbuffer a rrel rrel (U32.v len))
    (requires fun h ->
      HS.live_region h (rid_of_drgn r) /\
      U32.v from + U32.v len <= B.length src /\
      B.live h src)
    (ensures fun h0 b h1 ->
      B.alloc_post_mem_common b h0 h1
        (Seq.slice (B.as_seq h0 src) (U32.v from) (U32.v from + U32.v len)) /\
      B.frameOf b == rid_of_drgn r /\
      region_lifetime_buf r b)


/// Allocating a buffer that can be freed early
val ralloc_mm_buf (#a:Type0) (#rrel:B.srel a) (r:drgn) (init:a) (len:U32.t)
  : HST.ST (B.lmbuffer a rrel rrel (U32.v len))
    (requires fun h ->
      U32.v len > 0 /\
      HS.live_region h (rid_of_drgn r))
    (ensures fun h0 b h1 ->
      B.alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init) /\
      B.frameOf b == rid_of_drgn r)

/// Allocating a region-lifetime buffer, initializing its contents
/// with another buffer
val ralloc_and_blit_mm_buf (#a:Type0) (#rrel:B.srel a) (r:drgn)
  (#rrel1 #rel1:_) (src:B.mbuffer a rrel1 rel1) (from len:U32.t)
  : HST.ST (B.lmbuffer a rrel rrel (U32.v len))
    (requires fun h ->
      HS.live_region h (rid_of_drgn r) /\
      U32.v from + U32.v len <= B.length src /\
      B.live h src)
    (ensures fun h0 b h1 ->
      B.alloc_post_mem_common b h0 h1
        (Seq.slice (B.as_seq h0 src) (U32.v from) (U32.v from + U32.v len)) /\
      B.frameOf b == rid_of_drgn r)
