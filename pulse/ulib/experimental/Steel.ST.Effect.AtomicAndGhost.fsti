(*
   Copyright 2020 Microsoft Research

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

module Steel.ST.Effect.AtomicAndGhost

open Steel.Memory
module T = FStar.Tactics
include Steel.Effect.Common
module STF = Steel.ST.Effect

/// This module defines atomic and ghost variants of the Steel effect

#set-options "--warn_error -330 --ide_id_info_off"  //turn off the experimental feature warning

(*** SteelAGCommon effect ***)

/// The underlying representation of atomic and ghost computations, very similar to Steel
/// computations in Steel.Effect.
/// The opened_invariants index corresponds to the set of currently opened invariants,
/// and is relevant to the with_invariant combinator below
/// The observability bit will always be Unobservable for ghost computations
val repr (a:Type u#a)
         (already_framed:bool)
         (opened_invariants:inames)
         (g:observability)
         (pre:pre_t)
         (post:post_t a)
         (req:Type0)
         (ens:a -> Type0)
  : Type u#(max a 2)

/// Monadic return combinator for the Steel effect. It is parametric in the postcondition
/// The vprop precondition is annotated with the return_pre predicate to enable special handling,
/// as explained in Steel.Effect.Common
val return_ (a:Type u#a)
            (x:a)
            (opened_invariants:inames)
            (#[@@@ framing_implicit] p:a -> vprop)
  : repr a true opened_invariants Unobservable
         (return_pre (p x)) p
         True
         (fun v -> v == x)

val bind (a:Type) (b:Type)
         (opened_invariants:inames)
         (o1:eqtype_as_type observability)
         (o2:eqtype_as_type observability)
         (#framed_f:eqtype_as_type bool)
         (#framed_g:eqtype_as_type bool)
         (#[@@@ framing_implicit] pre_f:pre_t)
         (#[@@@ framing_implicit] post_f:post_t a)
         (#[@@@ framing_implicit] req_f:Type0)
         (#[@@@ framing_implicit] ens_f:a -> Type0)
         (#[@@@ framing_implicit] pre_g:a -> pre_t)
         (#[@@@ framing_implicit] post_g:a -> post_t b)
         (#[@@@ framing_implicit] req_g:(a -> Type0))
         (#[@@@ framing_implicit] ens_g:(a -> b -> Type0))
         (#[@@@ framing_implicit] frame_f:vprop)
         (#[@@@ framing_implicit] frame_g:a -> vprop)
         (#[@@@ framing_implicit] post:post_t b)
         (#[@@@ framing_implicit] _ : squash (maybe_emp framed_f frame_f))
         (#[@@@ framing_implicit] _ : squash (maybe_emp_dep framed_g frame_g))
         (#[@@@ framing_implicit] pr:a -> prop)
         (#[@@@ framing_implicit] p1:squash
           (can_be_split_forall_dep pr
             (fun x -> post_f x `star` frame_f)
             (fun x -> pre_g x `star` frame_g x)))
         (#[@@@ framing_implicit] p2:squash
           (can_be_split_post
             (fun x y -> post_g x y `star` frame_g x) post))
         (f:repr a framed_f opened_invariants o1 pre_f post_f req_f ens_f)
         (g:(x:a -> repr b framed_g opened_invariants o2 (pre_g x) (post_g x) (req_g x) (ens_g x)))
 : Pure (repr b
              true
              opened_invariants
              (join_obs o1 o2)
              (pre_f `star` frame_f)
              post
              (STF.bind_req a req_f ens_f pr req_g)
              (STF.bind_ens a b ens_f ens_g))
        (requires obs_at_most_one o1 o2)
        (ensures fun _ -> True)

val subcomp (a:Type)
            (opened_invariants:inames)
            (o1:eqtype_as_type observability)
            (o2:eqtype_as_type observability)
            (#framed_f:eqtype_as_type bool)
            (#framed_g:eqtype_as_type bool)
            (#[@@@ framing_implicit] pre_f:pre_t)
            (#[@@@ framing_implicit] post_f:post_t a)
            (#[@@@ framing_implicit] req_f:Type0)
            (#[@@@ framing_implicit] ens_f:a -> Type0)
            (#[@@@ framing_implicit] pre_g:pre_t)
            (#[@@@ framing_implicit] post_g:post_t a)
            (#[@@@ framing_implicit] req_g:Type0)
            (#[@@@ framing_implicit] ens_g:a -> Type0)
            (#[@@@ framing_implicit] frame:vprop)
            (#[@@@ framing_implicit] _ : squash (maybe_emp framed_f frame))
            (#[@@@ framing_implicit] p1:squash (can_be_split pre_g (pre_f `star` frame)))
            (#[@@@ framing_implicit] p2:squash (equiv_forall post_g (fun x -> post_f x `star` frame)))
            (f:repr a framed_f opened_invariants o1 pre_f post_f req_f ens_f)
: Pure (repr a framed_g opened_invariants o2 pre_g post_g req_g ens_g)
  (requires
    (o1 = Unobservable || o2 = Observable) /\
    (req_g ==> (req_f /\ (forall x. ens_f x ==> ens_g x))))
  (ensures fun _ -> True)

let if_then_else (a:Type)
                 (o:inames)
                 (#framed_f:eqtype_as_type bool)
                 (#framed_g:eqtype_as_type bool)
                 (#[@@@ framing_implicit] pre_f:pre_t)
                 (#[@@@ framing_implicit] pre_g:pre_t)
                 (#[@@@ framing_implicit] post_f:post_t a)
                 (#[@@@ framing_implicit] post_g:post_t a)
                 (#[@@@ framing_implicit] req_then:Type0)
                 (#[@@@ framing_implicit] ens_then:a -> Type0)
                 (#[@@@ framing_implicit] req_else:Type0)
                 (#[@@@ framing_implicit] ens_else:a -> Type0)
                 (#[@@@ framing_implicit] frame_f : vprop)
                 (#[@@@ framing_implicit] frame_g : vprop)
                 (#[@@@ framing_implicit] me1 : squash (maybe_emp framed_f frame_f))
                 (#[@@@ framing_implicit] me2 : squash (maybe_emp framed_g frame_g))
                 (#[@@@ framing_implicit] s_pre: squash (
                   can_be_split (pre_f `star` frame_f) (pre_g `star` frame_g)))
                 (#[@@@ framing_implicit] s_post: squash (
                   equiv_forall (fun x -> post_f x `star` frame_f) (fun x -> post_g x `star` frame_g)))
                 (f:repr a framed_f o Unobservable pre_f post_f req_then ens_then)
                 (g:repr a framed_g o Unobservable pre_g post_g req_else ens_else)
                 (p:bool)
  : Type
  = repr a true o Unobservable
         (pre_f `star` frame_f)
         (fun x -> post_f x `star` frame_f)
         (if p then req_then else req_else)
         (fun x -> if p then ens_then x else ens_else x)

/// Assembling the combinators defined above into an actual effect
/// The total keyword ensures that all ghost and atomic computations terminate.
[@@ ite_soundness_by ite_attr]
total
reflectable
effect {
  STAGCommon (a:Type)
             (framed:bool)
             (opened_invariants:inames)
             (o:observability)
             (pre:pre_t)
             (post:post_t a)
             (req:Type0)
             (ens:a -> Type0)
  with { repr = repr;
         return = return_;
         bind = bind;
         subcomp = subcomp;
         if_then_else = if_then_else }
}


/// The composition combinator.
val bind_pure_stag (a:Type) (b:Type)
                   (opened_invariants:inames)
                   (o:eqtype_as_type observability)
                   (#[@@@ framing_implicit] wp:pure_wp a)
                   (#framed:eqtype_as_type bool)
                   (#[@@@ framing_implicit] pre:pre_t)
                   (#[@@@ framing_implicit] post:post_t b)
                   (#[@@@ framing_implicit] req:a -> Type0)
                   (#[@@@ framing_implicit] ens:a -> b -> Type0)
                   (f:eqtype_as_type unit -> PURE a wp)
                   (g:(x:a -> repr b framed opened_invariants o pre post (req x) (ens x)))
: repr b
    framed opened_invariants o
    pre
    post
    (STF.bind_pure_st_req wp req)
    (STF.bind_pure_st_ens wp ens)


/// If the set of currently opened invariants is empty, an atomic Steel computation can be lifted
/// to a generic Steel computation.
/// Note that lifts are transitive in the effect lattice; hence a Steel ghost computation
/// will automatically be lifted to a generic Steel computation if needed by successively applying the lift from ghost to atomic computations, followed by the lift from atomic to generic steel computations, as long as all preconditions are satisfied
val lift_atomic_st
  (a:Type)
  (o:eqtype_as_type observability)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre:pre_t)
  (#[@@@ framing_implicit] post:post_t a)
  (#[@@@ framing_implicit] req:Type0)
  (#[@@@ framing_implicit] ens:a -> Type0)
  (f:repr a framed Set.empty o pre post req ens)
  : Steel.ST.Effect.repr a framed pre post req ens
