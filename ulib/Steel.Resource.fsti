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
module Steel.Resource

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module A = LowStar.Array

/// Resources are the fundamental abstraction of Steel, the framework that allows reasonning on Low*
/// program with separation logic concepts. They rely on the premice that most functions only talk
/// about and modify a small portion of the heap, and the effect used to specify those function
/// should have a structured way to talk about these small footprints as opposed to passing the
/// entire heap as it is done in the `ST` effect.
///
/// Resources are built upon `LowStar.Array`, which is our low-level model of memory allocations
/// unit.

(**** Views and resources *)


/// The first concept is the heap invariant. We want to be able to attach invariants to heap
/// objects, that are maintained throughtout the program
let inv_t = HS.mem -> prop
let imem (inv: inv_t) = m:HS.mem{inv m}

/// The second concept is the footprint. It is simply a location as defined in
/// `LowStar.Array.Modifies`.
let fp_t = (h:HS.mem) -> GTot A.loc
let as_loc (fp:fp_t) (h: HS.mem) : GTot A.loc = fp h

/// The third concept is the selector. Each memory footprint represents a high-level object, which
/// we call the view attached to this footprint. This view is provided by a selector, abbreviated
/// `sel`, which reads a heap satisfying an invariant.
///
/// These three concepts form the resource trinity. A resource is a memory footprint satisfying an
/// invariant valable for any heap, from which you can extract a view.
unfold
let sel_t (a: Type) = HS.mem -> GTot a

val fp_reads_fp (fp: fp_t) (inv: inv_t) : prop

/// `sel_reads_fp` reformulate the core principle of the `modifies` theory: resource views should be
/// preserved as long as the resource footprint is not part of the modified area.
val sel_reads_fp (#b: Type) (fp: fp_t) (inv:inv_t) (sel:imem inv -> GTot b) : prop


/// Similarly, invariants should be preserved when the footprint is not modified.
val inv_reads_fp (fp: fp_t) (inv:inv_t) : prop

/// Armed with this concept, we can define the core definition of the resource framework : the view.
/// The view combines invariant, footprint and selector into a coherent object that behaves nicely
/// with respect to the modifies theory
noeq type view_aux (a: Type) = {
  fp: fp_t;
  inv: inv_t;
  sel: sel_t a
}
let view (a: Type) = view:view_aux a{
  fp_reads_fp view.fp view.inv /\
  sel_reads_fp view.fp view.inv view.sel /\
  inv_reads_fp view.fp view.inv
}


/// While the resource is abstract, we provide `reveal` methods that allow you to interoperate
/// resources with regular modifies-based Low*.
val reveal_view (_ : unit)
  : Lemma (
    (forall (fp: fp_t) (inv: inv_t). {:pattern fp_reads_fp fp inv}
      fp_reads_fp fp inv <==>
      (forall (h0 h1: HS.mem) (loc: A.loc). {:pattern (A.modifies loc h0 h1); (fp h1); inv h0 }
        A.loc_disjoint (as_loc fp h0) loc /\
        A.modifies loc h0 h1 /\ inv h0 ==>
          as_loc fp h0 == as_loc fp h1
      )
    ) /\
    (forall (#b: Type) (fp: fp_t) (inv:inv_t) (sel:sel_t b) . {:pattern sel_reads_fp fp inv sel}
      sel_reads_fp fp inv sel <==>
      (forall (h0 h1:imem inv) (loc: A.loc). {:pattern  (A.modifies loc h0 h1); (sel h1)}
        A.loc_disjoint (as_loc fp h0) loc /\ A.modifies loc h0 h1 ==>
          sel h0 == sel h1
      )
    ) /\
    (forall (fp: fp_t) (inv: inv_t). {:pattern inv_reads_fp fp inv}
      inv_reads_fp fp inv <==>
      (forall (h0 h1: HS.mem) (loc: A.loc). {:pattern (A.modifies loc h0 h1); (inv h1)}
        inv h0 /\ A.loc_disjoint (as_loc fp h0) loc /\ A.modifies loc h0 h1 ==>
          inv h1
      )
    )
  )

/// The resource type is polymorhpic, offering a unified way to talk about any heap object.

[@erasable]
noeq type resource : Type u#1 = {
  t: Type u#0;
  view: view t
}

let as_resource (#a:Type) (view:view a) : resource = {
  t = a;
  view = view
}

/// Helper functions to get the components of a resource

let view_of (res:resource) : GTot (view res.t) =
  res.view

let fp (res:resource) : GTot fp_t =
  res.view.fp

let inv (res:resource) (h:HS.mem) : GTot prop =
  res.view.inv h

let sel (#a:Type) (view:view a) (h: HS.mem) : GTot a =
  view.sel h

(**** Separating conjunction on views and resources *)

/// Core operator, offering a flavor of separation logic for resources. `res1 <*> res2` is a new
/// resource whose footprint is the disjoint union of those of `res1` and `res2`, the invariant is
/// the conjunction of the two invariants and the view is the pair of the two.
val ( <*> ) (res1 res2:resource) : res:resource

/// DA: we might consider removing this SMTPat at the cost of having to have expicitly call reveals
/// in specs involving <*>.
val reveal_star_inv (res1 res2:resource) (h:HS.mem)
  : Lemma (
    (inv (res1 <*> res2) h) <==>
      (inv res1 h /\ inv res2 h /\ A.loc_disjoint (as_loc (fp res1) h) (as_loc (fp res2) h))
  )
  [SMTPat (inv (res1 <*> res2) h)]

val reveal_star_sel (res1 res2:resource) (h:HS.mem)
  : Lemma (
      sel (view_of (res1 <*> res2)) h ===
        (sel (view_of res1) h, sel (view_of res2) h)
  )
  [SMTPat (sel (view_of (res1 <*> res2)) h)]

val reveal_star (_: unit)
  : Lemma (
    (forall res1 res2 h .{:pattern as_loc (fp (res1 <*> res2)) h}
      as_loc (fp (res1 <*> res2)) h == A.loc_union (as_loc (fp res1) h) (as_loc (fp res2) h )
    ) /\
    (forall res1 res2 .{:pattern (res1 <*> res2).t}
      (res1 <*> res2).t == res1.t & res2.t
    ) /\
    (forall res1 res2 h .{:pattern (res1 <*> res2).view.sel h}
       (res1 <*> res2).view.sel h == (sel res1.view h,sel res2.view h)
    )
  )

(**** Empty resource *)

val empty_resource: resource

val reveal_empty_resource (_ : unit)
  : Lemma (
    (forall h. {:pattern fp empty_resource h} fp empty_resource h == A.loc_none) /\
    (forall h .{:pattern inv empty_resource h} inv empty_resource h <==> True) /\
    (empty_resource.t == unit) /\
    (forall h .{:pattern sel empty_resource.view h} sel empty_resource.view h == ())
  )

(**** Splitting resources *)

/// Splitting resources into smaller constituents. Its main use case is for stating resource
/// inclusion for framing, where by
/// ```
/// res1 `can_be_split_into` (res2,res3)
/// ```
/// we intuitively mean that the inner (re framing) resource `res2` is included in the outer
/// (re framing) resource `res1`, as witnessed by `res3` that is the formal delta-resource `res3`.

/// The footprint of the outer resource is union of delta and the inner resource. The outer
/// invariant is equivalent to delta and the inner invariant (when they are disjoint).
val can_be_split_into (outer:resource) (inner_delta:resource & resource) : prop

val reveal_can_be_split_into (_ : unit)
  : Lemma (forall (outer inner delta: resource) .
    outer `can_be_split_into` (inner,delta) <==>
      (forall (h: HS.mem).
        (as_loc (fp outer) h == A.loc_union (as_loc (fp delta) h) (as_loc (fp inner) h)) /\
        (inv outer h <==>
          inv inner h /\ inv delta h /\ A.loc_disjoint (as_loc (fp delta) h) (as_loc (fp inner) h))
      )
  )

/// SMT-patterns to reveal some of the properties of abstract can_be_split_into in specs

val star_can_be_split_into_parts (res1 res2:resource)
  : Lemma ((res1 <*> res2) `can_be_split_into` (res1,res2))
  [SMTPat (can_be_split_into (res1 <*> res2) (res1,res2))]

val star_can_be_split_into_parts' (res1 res2:resource)
  : Lemma (can_be_split_into (res1 <*> res2) (res2,res1))
  [SMTPat ((res1 <*> res2) `can_be_split_into` (res2,res1))]

val can_be_split_into_empty_left (res:resource)
  : Lemma (res `can_be_split_into` (empty_resource,res))
  [SMTPat (res `can_be_split_into` (empty_resource,res))]

val can_be_split_into_empty_reverse_left (res1 res2:resource)
  : Lemma ((res1 <*> res2) `can_be_split_into` (empty_resource,res2 <*> res1 ))
  [SMTPat ((res1 <*> res2) `can_be_split_into` (empty_resource,res2 <*> res1))]

val can_be_split_into_empty_right (res:resource)
  : Lemma (res `can_be_split_into` (res,empty_resource))
  [SMTPat (res `can_be_split_into` (res,empty_resource))]

val can_be_split_into_empty_reverse_right (res1 res2:resource)
  : Lemma ((res1 <*> res2) `can_be_split_into` (res2 <*> res1, empty_resource))
  [SMTPat ((res1 <*> res2) `can_be_split_into` (res2 <*> res1, empty_resource))]

val reveal_can_be_split_into_inner_inv (outer inner delta:resource) (h:HS.mem)
  : Lemma
    (requires (outer `can_be_split_into` (inner,delta) /\ inv outer h))
    (ensures  (inv inner h))
  [SMTPat (outer `can_be_split_into` (inner,delta)); SMTPat (inv inner h)]

val reveal_can_be_split_into_delta_inv (outer inner delta:resource) (h:HS.mem)
  : Lemma
    (requires (outer `can_be_split_into` (inner,delta) /\ inv outer h))
    (ensures  (inv delta h))
  [SMTPat (outer `can_be_split_into` (inner,delta)); SMTPat (inv delta h)]

(**** Equivalence relation (extensional equality) on resources *)

val equal (res1 res2: resource) : prop

val equal_refl (res:resource)
  : Lemma (res `equal` res)

val equal_symm (res1 res2:resource)
  : Lemma
    (requires (res1 `equal` res2))
    (ensures  (res2 `equal` res1))

val equal_trans (res1 res2 res3:resource)
  : Lemma
    (requires (res1 `equal` res2 /\ res2 `equal` res3))
    (ensures  (res1 `equal` res3))

/// Resources form a commutative monoid (up to `equal`)

val equal_comm_monoid_left_unit (res:resource)
  : Lemma ((empty_resource <*> res) `equal` res)

val equal_comm_monoid_right_unit (res:resource)
  : Lemma ((res <*> empty_resource) `equal` res)

val equal_comm_monoid_commutativity (res1 res2:resource)
  : Lemma ((res1 <*> res2) `equal` (res2 <*> res1))

val equal_comm_monoid_associativity (res1 res2 res3:resource)
  : Lemma (((res1 <*> res2) <*> res3) `equal` (res1 <*> (res2 <*> res3)))

/// `equal` is also a congruence with respect to `(empty_resource, <*>)`

val equal_comm_monoid_cong (res1 res2 res3 res4:resource)
  : Lemma
    (requires (res1 `equal` res3 /\ res2 `equal` res4))
    (ensures  ((res1 <*> res2) `equal` (res3 <*> res4)))

/// `can_be_split_into` follows from equality to `<*>` (called in frame resolution)

val can_be_split_into_star (res1 res2 res3:resource)
  : Lemma
    (requires ((res2 <*> res3) `equal` res1))
    (ensures  (res1 `can_be_split_into` (res2,res3)))
