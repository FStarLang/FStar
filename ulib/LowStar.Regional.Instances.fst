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

module LowStar.Regional.Instances

open FStar.Integers
open LowStar.Buffer
open LowStar.Regional
open LowStar.RVector

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module S = FStar.Seq
module B = LowStar.Buffer
module V = LowStar.Vector
module RV = LowStar.RVector

/// `LowStar.Buffer` is regional

val buffer_region_of:
  #a:Type -> v:B.buffer a -> GTot HS.rid
let buffer_region_of #a v =
  B.frameOf v

val buffer_dummy: a:Type -> Tot (B.buffer a)
let buffer_dummy _ = B.null

let nonzero = len:UInt32.t{len > 0ul}

val buffer_r_inv:
  #a:Type -> len:nonzero ->
  h:HS.mem -> v:B.buffer a -> GTot Type0
let buffer_r_inv #a len h v =
  B.live h v /\ B.freeable v /\
  B.len v == len

val buffer_r_inv_reg:
  #a:Type -> len:nonzero ->
  h:HS.mem -> v:B.buffer a ->
  Lemma (requires (buffer_r_inv len h v))
        (ensures (HS.live_region h (buffer_region_of v)))
let buffer_r_inv_reg #a len h v = ()

val buffer_repr: a:Type0 -> len:nat{len > 0} -> Type0
let buffer_repr a len = s:S.seq a{S.length s = len}

val buffer_r_repr:
  #a:Type -> len:UInt32.t{len > 0ul} ->
  h:HS.mem -> v:B.buffer a{buffer_r_inv len h v} ->
  GTot (buffer_repr a (UInt32.v len))
let buffer_r_repr #a len h v = B.as_seq h v

val buffer_r_sep:
  #a:Type -> len:UInt32.t{len > 0ul} ->
  v:B.buffer a -> p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (buffer_r_inv len h0 v /\
                  loc_disjoint
                    (loc_all_regions_from false
                      (buffer_region_of v)) p /\
                  modifies p h0 h1))
        (ensures (buffer_r_inv len h1 v /\
                 buffer_r_repr len h0 v == buffer_r_repr len h1 v))
let buffer_r_sep #a len v p h0 h1 =
  assert (loc_includes (loc_all_regions_from false (buffer_region_of v))
                       (loc_buffer v));
  B.modifies_buffer_elim v p h0 h1

val buffer_irepr:
  #a:Type0 -> ia:a -> len:UInt32.t{len > 0ul} ->
  Ghost.erased (buffer_repr a (UInt32.v len))
let buffer_irepr #a ia len =
  Ghost.hide (S.create (UInt32.v len) ia)

val buffer_r_alloc_p:
  #a:Type0 -> v:B.buffer a -> GTot Type0
let buffer_r_alloc_p #a v =
  True

/// This is the key example here that illustrates how to efficiently do
/// closure-conversion by hand: we have at run-time a function that takes
/// ``arg`` (an actual parameter) that contains the closure state. However, if
/// the function only takes ``arg``, it will have a type that is too
/// polymorphic, i.e. it'll have type ``forall arg. arg -> ...``. Therefore, we
/// add ``arg'`` which is an erased, type-only index which, once instantiated,
/// restricts the domain of the function to operate on the sole value being
/// captured.
val buffer_r_alloc:
  #a:Type -> #arg':Ghost.erased (a & nonzero) -> arg:(a & nonzero) { arg == Ghost.reveal arg' } -> r:HST.erid ->
  HST.ST (B.buffer a)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 ->
      let ia = fst arg in
      let len = snd arg in
      Set.subset (Map.domain (HS.get_hmap h0))
                 (Map.domain (HS.get_hmap h1)) /\
      modifies loc_none h0 h1 /\
      fresh_loc (B.loc_buffer v) h0 h1 /\
      buffer_r_alloc_p v /\
      buffer_r_inv len h1 v /\
      buffer_region_of v = r /\
      buffer_r_repr len h1 v == Ghost.reveal (buffer_irepr ia len)))
let buffer_r_alloc #a #_ (ia, len) r =
  B.malloc r ia len

val buffer_r_free:
  #a:Type ->
  #arg':Ghost.erased (a & nonzero) ->
  arg:(a & nonzero) { arg == Ghost.reveal arg' } ->
  v:B.buffer a ->
  HST.ST unit
    (requires (fun h0 ->
      let ia = fst arg in
      let len = snd arg in
      buffer_r_inv len h0 v))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (buffer_region_of v)) h0 h1))
let buffer_r_free #a len v =
  B.free v

val buffer_copy:
  #a:Type ->
  #arg':Ghost.erased (a & nonzero) ->
  arg:(a & nonzero){ arg == Ghost.reveal arg' } ->
  src:B.buffer a -> dst:B.buffer a ->
  HST.ST unit
    (requires (fun h0 ->
      let len = snd arg in
      buffer_r_inv len h0 src /\ buffer_r_inv len h0 dst /\
      HS.disjoint (buffer_region_of src) (buffer_region_of dst)))
    (ensures (fun h0 _ h1 ->
      let len = snd arg in
      modifies (loc_all_regions_from false (buffer_region_of dst)) h0 h1 /\
      buffer_r_inv len h1 dst /\
      buffer_r_repr len h1 dst == buffer_r_repr len h0 src))
let buffer_copy #a #_ (ia, len) src dst =
  B.blit src 0ul dst 0ul len

#set-options "--print_implicits"
val buffer_regional:
  #a:Type -> ia:a -> len:nonzero ->
  regional (a & nonzero) (B.buffer a)
let buffer_regional #a ia len =
  Rgl (ia, len)
      (buffer_region_of #a)
      B.loc_buffer
      (buffer_dummy a)
      (buffer_r_inv #a len)
      (buffer_r_inv_reg #a len)
      (buffer_repr a (UInt32.v len))
      (buffer_r_repr #a len)
      (buffer_r_sep #a len)
      (buffer_irepr #a ia len)
      (buffer_r_alloc_p #a)
      // This is key: there is no partial application here, meaning this extracts to C.
      (buffer_r_alloc #a #(ia, len))
      (buffer_r_free #a #(ia, len))



val buffer_copyable:
  #a:Type -> ia:a -> len:nonzero ->
  copyable #(a & nonzero) (B.buffer a) (buffer_regional ia len)
let buffer_copyable #a ia len =
  Cpy (buffer_copy #_ #(ia, len))

/// If `a` is regional, then `vector a` is also regional.
///
/// We keep a pointer at run-time to the parent type-class.

val vector_region_of:
  #a:Type0 -> #rst:Type -> rg:regional rst a -> v:rvector rg -> GTot HS.rid
let vector_region_of #a #rst rg v = V.frameOf v

val vector_dummy:
  #a:Type0 -> #rst:Type -> rg:Ghost.erased (regional rst a) -> Tot (rvector rg)
let vector_dummy #a #_ _ = V.alloc_empty a

val vector_r_inv:
  #a:Type0 -> #rst:Type -> rg:regional rst a ->
  h:HS.mem -> v:rvector rg -> GTot Type0
let vector_r_inv #a #rst rg h v = RV.rv_inv h v

val vector_r_inv_reg:
  #a:Type0 -> #rst:Type -> rg:regional rst a ->
  h:HS.mem -> v:rvector rg ->
  Lemma (requires (vector_r_inv rg h v))
        (ensures (HS.live_region h (vector_region_of rg v)))
let vector_r_inv_reg #a #rst rg h v = ()

val vector_repr: #a:Type0 -> #rst:Type -> rg:regional rst a -> Tot Type0
let vector_repr #a #rst rg = S.seq (Rgl?.repr rg)

val vector_r_repr:
  #a:Type0 -> #rst:Type -> rg:regional rst a ->
  h:HS.mem -> v:rvector rg{vector_r_inv rg h v} ->
  GTot (vector_repr rg)
let vector_r_repr #a #rst rg h v = RV.as_seq h v

val vector_r_sep:
  #a:Type0 -> #rst:Type -> rg:regional rst a ->
  v:rvector rg -> p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (vector_r_inv rg h0 v /\
                  loc_disjoint
                    (loc_all_regions_from false (vector_region_of rg v))
                    p /\
                  modifies p h0 h1))
        (ensures (vector_r_inv rg h1 v /\
                 vector_r_repr rg h0 v == vector_r_repr rg h1 v))
let vector_r_sep #a #rst rg v p h0 h1 =
  RV.rv_inv_preserved v p h0 h1;
  RV.as_seq_preserved v p h0 h1

val vector_irepr:
  #a:Type0 -> #rst:Type -> rg:regional rst a -> Ghost.erased (vector_repr rg)
let vector_irepr #a #rst rg =
  Ghost.hide S.empty

val vector_r_alloc_p:
  #a:Type0 -> #rst:Type -> rg:regional rst a -> v:rvector rg -> GTot Type0
let vector_r_alloc_p #a #rst rg v =
  V.size_of v = 0ul

val vector_r_alloc:
  #a:Type0 -> #rst:Type -> rg:regional rst a -> r:HST.erid ->
  HST.ST (rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 ->
      Set.subset (Map.domain (HS.get_hmap h0))
                 (Map.domain (HS.get_hmap h1)) /\
      modifies loc_none h0 h1 /\
      fresh_loc (V.loc_vector v) h0 h1 /\
      vector_r_alloc_p rg v /\
      vector_r_inv rg h1 v /\
      vector_region_of rg v = r /\
      vector_r_repr rg h1 v == Ghost.reveal (vector_irepr rg)))
let vector_r_alloc #a #rst rg r =
  let nrid = HST.new_region r in
  V.alloc_reserve 1ul (rg_dummy rg) r

val vector_r_free:
  #a:Type0 -> #rst:Type -> #rg:Ghost.erased (regional rst a) -> (s:regional rst a{s == Ghost.reveal rg}) -> v:rvector rg ->
  HST.ST unit
    (requires (fun h0 -> vector_r_inv rg h0 v))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (vector_region_of rg v)) h0 h1))
let vector_r_free #_ #_ _ v =
  V.free v

val vector_regional:
  #a:Type0 -> #rst:Type -> rg:regional rst a -> regional (regional rst a) (rvector rg)
let vector_regional #a #rst rg =
  Rgl rg
      (vector_region_of #a #rst rg)
      V.loc_vector
      (vector_dummy #a #rst rg)
      (vector_r_inv #a #rst rg)
      (vector_r_inv_reg #a #rst rg)
      (vector_repr #a rg)
      (vector_r_repr #a #rst rg)
      (vector_r_sep #a #rst rg)
      (vector_irepr #a rg)
      (vector_r_alloc_p #a #rst rg)
      (vector_r_alloc #a #rst)
      (vector_r_free #a #rst #rg)
