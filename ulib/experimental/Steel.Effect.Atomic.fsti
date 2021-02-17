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


module Steel.Effect.Atomic
open FStar.PCM
open Steel.Memory
include Steel.Effect.Common

#set-options "--warn_error -330"  //turn off the experimental feature warning

val observability : Type0
val has_eq_observability (_:unit) : Lemma (hasEq observability)
val observable : observability
val unobservable : observability

let obs_at_most_one o1 o2 =
  o1==unobservable \/ o2==unobservable

let join_obs (o1:observability) (o2:observability) =
  has_eq_observability();
  if observable = o1 || observable = o2
  then observable
  else unobservable

val atomic_repr (a:Type u#a)
   (opened_invariants:inames)
   (g:observability)
   (pre:slprop u#1)
   (post:a -> slprop u#1)
   (req:req_t pre)
   (ens:ens_t pre a post)
  : Type u#(max a 2)

unfold
let return_req (p:slprop u#1) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> slprop u#1) : ens_t (p x) a p = fun _ r _ -> r == x

val return (a:Type u#a)
   (x:a)
   (opened_invariants:inames)
   (#[@@@ framing_implicit] p:a -> slprop u#1)
  : atomic_repr a opened_invariants unobservable
                (return_pre (p x)) (return_post p)
                (return_req (p x)) (return_ens a x p)

unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (_:squash (can_be_split_forall post_f pre_g))
: req_t pre_f
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (post:post_t b)
  (_:squash (can_be_split_forall post_f pre_g))
  (_:squash (can_be_split_post post_g post))
: ens_t pre_f b post
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

val bind (a:Type u#a) (b:Type u#b)
   (opened_invariants:inames)
   (o1:observability)
   (o2:observability)
   (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
   (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
   (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
   (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
   (#[@@@ framing_implicit] post:post_t b)
   (#[@@@ framing_implicit] p1:squash (can_be_split_forall post_f pre_g))
   (#[@@@ framing_implicit] p2:squash (can_be_split_post post_g post))
   (f:atomic_repr a opened_invariants o1 pre_f post_f req_f ens_f)
   (g:(x:a -> atomic_repr b opened_invariants o2 (pre_g x) (post_g x) (req_g x) (ens_g x)))
  : Pure (atomic_repr b opened_invariants (join_obs o1 o2)
                      pre_f post
                      (bind_req req_f ens_f req_g p1)
                      (bind_ens req_f ens_f ens_g post p1 p2)
                      )
         (requires obs_at_most_one o1 o2)
         (ensures fun _ -> True)

unfold
let subcomp_pre (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (can_be_split pre_g pre_f))
  (_:squash (can_be_split_forall post_f post_g))
: pure_pre
= (forall (m0:hmem pre_g). req_g m0 ==> req_f m0) /\
  (forall (m0:hmem pre_g) (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> ens_g m0 x m1)

val subcomp (a:Type)
  (opened_invariants:inames)
  (o1:observability)
  (o2:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:pre_t) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_g:req_t pre_g) (#[@@@ framing_implicit] ens_g:ens_t pre_g a post_g)
  (#[@@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@@ framing_implicit] p2:squash (can_be_split_forall post_f post_g))
  (f:atomic_repr a opened_invariants o1 pre_f post_f req_f ens_f)
: Pure (atomic_repr a opened_invariants o2 pre_g post_g req_g ens_g)
       (requires (o1 == observable ==> o2 == observable) /\
         subcomp_pre req_f ens_f req_g ens_g p1 p2)
       (ensures fun _ -> True)

// let if_then_else (a:Type)
//   (opened_invariants:inames)
//   (o:observability)
//   (#[@@framing_implicit] pre:pre_t) (#[@@framing_implicit] post:post_t a)
//   (f:atomic_repr a opened_invariants o pre post)
//   (g:atomic_repr a opened_invariants o pre post)
//   (p:Type0)
//   : Type
//   = atomic_repr a opened_invariants o pre post

[@@allow_informative_binders]
total
reifiable reflectable
layered_effect {
  SteelAtomicF : a:Type
              -> opened_invariants:inames
              -> o:observability
              -> pre:slprop u#1
              -> post:(a -> slprop u#1)
              -> req:req_t pre
              -> ens:ens_t pre a post
              -> Effect
  with
  repr = atomic_repr;
  return = return;
  bind = bind;
  subcomp = subcomp
  // if_then_else = if_then_else
}

[@@allow_informative_binders]
total
reifiable reflectable
new_effect SteelAtomic = SteelAtomicF

unfold
let bind_steela_steela_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:slprop) (frame_g:a -> slprop)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steela_steela_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:slprop) (frame_g:a -> slprop)
  (post:post_t b)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

val bind_steela_steela (a:Type) (b:Type)
  (opened_invariants:inames)
  (o1:observability)
  (o2:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_f:slprop) (#[@@@ framing_implicit] frame_g:a -> slprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:atomic_repr a opened_invariants o1 pre_f post_f req_f ens_f)
  (g:(x:a -> atomic_repr b opened_invariants o2 (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Pure (atomic_repr b opened_invariants (join_obs o1 o2)
      (pre_f `star` frame_f)
      post
      (bind_steela_steela_req req_f ens_f req_g frame_f frame_g p)
      (bind_steela_steela_ens req_f ens_f ens_g frame_f frame_g post p p2)
    )
    (requires obs_at_most_one o1 o2)
    (ensures fun _ -> True)

polymonadic_bind (SteelAtomic, SteelAtomic) |> SteelAtomicF = bind_steela_steela

unfold
let bind_steela_steelaf_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:slprop)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steela_steelaf_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:slprop)
  (post:post_t b)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (_: squash (can_be_split_post post_g post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)


val bind_steela_steelaf (a:Type) (b:Type)
  (opened_invariants:inames)
  (o1:observability)
  (o2:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_f:slprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post post_g post))
  (f:atomic_repr a opened_invariants o1 pre_f post_f req_f ens_f)
  (g:(x:a -> atomic_repr b opened_invariants o2 (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Pure (atomic_repr b opened_invariants (join_obs o1 o2)
         (pre_f `star` frame_f)
         post
        (bind_steela_steelaf_req req_f ens_f req_g frame_f p)
        (bind_steela_steelaf_ens req_f ens_f ens_g frame_f post p p2)
       )
       (requires obs_at_most_one o1 o2)
       (ensures fun _ -> True)

polymonadic_bind (SteelAtomic, SteelAtomicF) |> SteelAtomicF = bind_steela_steelaf

unfold
let bind_steelaf_steela_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_g:a -> slprop)
  (_:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
: req_t pre_f
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steelaf_steela_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_g:a -> slprop)
  (post:post_t b)
  (_:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t pre_f b post
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

val bind_steelaf_steela (a:Type) (b:Type)
  (opened_invariants:inames)
  (o1:observability)
  (o2:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_g:a -> slprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:atomic_repr a opened_invariants o1 pre_f post_f req_f ens_f)
  (g:(x:a -> atomic_repr b opened_invariants o2 (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Pure (atomic_repr b opened_invariants (join_obs o1 o2)
          pre_f
          post
         (bind_steelaf_steela_req req_f ens_f req_g frame_g p)
         (bind_steelaf_steela_ens req_f ens_f ens_g frame_g post p p2)
        )
    (requires obs_at_most_one o1 o2)
    (ensures fun _ -> True)

polymonadic_bind (SteelAtomicF, SteelAtomic) |> SteelAtomicF = bind_steelaf_steela

unfold
let bind_pure_steela__req (#a:Type) (wp:pure_wp a)
  (#pre:pre_t) (req:a -> req_t pre)
: req_t pre
= fun m -> wp (fun x -> (req x) m) /\ as_requires wp

unfold
let bind_pure_steela__ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre:pre_t) (#post:post_t b) (ens:a -> ens_t pre b post)
: ens_t pre b post
= fun m0 r m1 -> as_requires wp /\ (exists (x:a). as_ensures wp x /\ (ens x) m0 r m1)

val bind_pure_steela_ (a:Type) (b:Type)
  (opened_invariants:inames)
  (o:observability)
  (#[@@@ framing_implicit] wp:pure_wp a)
  (#[@@@ framing_implicit] pre:pre_t) (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] req:a -> req_t pre) (#[@@@ framing_implicit] ens:a -> ens_t pre b post)
  (f:eqtype_as_type unit -> PURE a wp)
  (g:(x:a -> atomic_repr b opened_invariants o pre post (req x) (ens x)))
: atomic_repr b opened_invariants o
    pre
    post
    (bind_pure_steela__req wp req)
    (bind_pure_steela__ens wp ens)

polymonadic_bind (PURE, SteelAtomicF) |> SteelAtomicF = bind_pure_steela_

polymonadic_bind (PURE, SteelAtomic) |> SteelAtomic = bind_pure_steela_

polymonadic_subcomp SteelAtomicF <: SteelAtomic = subcomp

effect SteelAtomicT (a:Type) (opened:inames) (o:observability) (pre:pre_t) (post:post_t a) =
  SteelAtomic a opened o pre post (fun _ -> True) (fun _ _ _ -> True)

(***** Bind and Subcomp relation with Steel.Atomic *****)

(** F, F -> F **)

val bind_steelatomicf_steelf (a:Type) (b:Type)
  (is_ghost:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x)))
  (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p1:squash (can_be_split_forall post_f pre_g))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post post_g post))
  (f:atomic_repr a Set.empty is_ghost pre_f post_f req_f ens_f)
  (g:(x:a -> Steel.Effect.repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b pre_f post
    (bind_req req_f ens_f req_g p1)
    (bind_ens req_f ens_f ens_g post p1 p2)

polymonadic_bind (SteelAtomicF, Steel.Effect.SteelF) |> Steel.Effect.SteelF = bind_steelatomicf_steelf


val bind_steelf_steelatomicf (a:Type) (b:Type)
  (o:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x)))
  (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p1:squash (can_be_split_forall post_f pre_g))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post post_g post))
  (f:Steel.Effect.repr a pre_f post_f req_f ens_f)
  (g:(x:a -> atomic_repr b Set.empty o (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b pre_f post
    (bind_req req_f ens_f req_g p1)
    (bind_ens req_f ens_f ens_g post p1 p2)

polymonadic_bind (Steel.Effect.SteelF, SteelAtomicF) |> Steel.Effect.SteelF = bind_steelf_steelatomicf

(** A, F -> F **)

val bind_steelatomic_steelf (a:Type) (b:Type)
  (o:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x)))
  (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_f:slprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (#[@@@ framing_implicit] p2: squash (can_be_split_post post_g post))
  (f:atomic_repr a Set.empty o pre_f post_f req_f ens_f)
  (g:(x:a -> Steel.Effect.repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b
    (pre_f `star` frame_f)
    post
    (bind_steela_steelaf_req req_f ens_f req_g frame_f p)
    (bind_steela_steelaf_ens req_f ens_f ens_g frame_f post p p2)


polymonadic_bind (SteelAtomic, Steel.Effect.SteelF) |> Steel.Effect.SteelF = bind_steelatomic_steelf

val bind_steel_steelatomicf (a:Type) (b:Type)
  (o:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x)))
  (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_f:slprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (#[@@@ framing_implicit] p2: squash (can_be_split_post post_g post))
  (f:Steel.Effect.repr a pre_f post_f req_f ens_f)
  (g:(x:a -> atomic_repr b Set.empty o (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b
    (pre_f `star` frame_f)
    post
    (bind_steela_steelaf_req req_f ens_f req_g frame_f p)
    (bind_steela_steelaf_ens req_f ens_f ens_g frame_f post p p2)

polymonadic_bind (Steel.Effect.Steel, SteelAtomicF) |> Steel.Effect.SteelF = bind_steel_steelatomicf

(** F, A -> F **)

val bind_steelf_steelatomic (a:Type) (b:Type)
  (o:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_g:a -> slprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:Steel.Effect.repr a pre_f post_f req_f ens_f)
  (g:(x:a -> atomic_repr b Set.empty o (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b
          pre_f
          post
         (bind_steelaf_steela_req req_f ens_f req_g frame_g p)
         (bind_steelaf_steela_ens req_f ens_f ens_g frame_g post p p2)

polymonadic_bind (Steel.Effect.SteelF, SteelAtomic) |> Steel.Effect.SteelF = bind_steelf_steelatomic

val bind_steelatomicf_steel (a:Type) (b:Type)
  (o:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_g:a -> slprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:atomic_repr a Set.empty o pre_f post_f req_f ens_f)
  (g:(x:a -> Steel.Effect.repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b
          pre_f
          post
         (bind_steelaf_steela_req req_f ens_f req_g frame_g p)
         (bind_steelaf_steela_ens req_f ens_f ens_g frame_g post p p2)

polymonadic_bind (SteelAtomicF, Steel.Effect.Steel) |> Steel.Effect.SteelF = bind_steelatomicf_steel

(** A, A -> F **)

val bind_steelatomic_steel (a:Type) (b:Type)
  (o:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x)))
  (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_f:slprop) (#[@@@ framing_implicit] frame_g:a -> slprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:atomic_repr a Set.empty o pre_f post_f req_f ens_f)
  (g:(x:a -> Steel.Effect.repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b
    (pre_f `star` frame_f)
    post
    (bind_steela_steela_req req_f ens_f req_g frame_f frame_g p)
    (bind_steela_steela_ens req_f ens_f ens_g frame_f frame_g post p p2)

polymonadic_bind (SteelAtomic, Steel.Effect.Steel) |> Steel.Effect.SteelF =
  bind_steelatomic_steel

val bind_steel_steelatomic (a:Type) (b:Type)
  (o:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x)))
  (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_f:slprop) (#[@@@ framing_implicit] frame_g:a -> slprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:Steel.Effect.repr a pre_f post_f req_f ens_f)
  (g:(x:a -> atomic_repr b Set.empty o (pre_g x) (post_g x) (req_g x) (ens_g x)))
: Steel.Effect.repr b
    (pre_f `star` frame_f)
    post
    (bind_steela_steela_req req_f ens_f req_g frame_f frame_g p)
    (bind_steela_steela_ens req_f ens_f ens_g frame_f frame_g post p p2)

polymonadic_bind (Steel.Effect.Steel, SteelAtomic) |> Steel.Effect.SteelF = bind_steel_steelatomic

(** subcomp **)

val subcomp_atomic_steel (a:Type) (is_ghost:observability)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:pre_t) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_g:req_t pre_g) (#[@@@ framing_implicit] ens_g:ens_t pre_g a post_g)
  (#[@@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@@ framing_implicit] p2:squash (can_be_split_forall post_f post_g))
  (f:atomic_repr a Set.empty is_ghost pre_f post_f req_f ens_f)
: Pure (Steel.Effect.repr a pre_g post_g req_g ens_g)
       (requires subcomp_pre req_f ens_f req_g ens_g p1 p2)
       (ensures fun _ -> True)

polymonadic_subcomp SteelAtomic <: Steel.Effect.Steel = subcomp_atomic_steel
polymonadic_subcomp SteelAtomicF <: Steel.Effect.Steel = subcomp_atomic_steel

[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action (#a:Type u#a)
                     (#opened_invariants:inames)
                     (#o:observability)
                     (#fp:slprop)
                     (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : SteelAtomicT a opened_invariants o fp fp'

val new_invariant (opened_invariants:inames) (p:slprop)
  : SteelAtomicT (inv p) opened_invariants unobservable p (fun _ -> emp)

let set_add i o : inames = Set.union (Set.singleton i) o
val with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#o:observability)
                   (#p:slprop)
                   (i:inv p{not (i `Set.mem` opened_invariants)})
                   ($f:unit -> SteelAtomicT a (set_add i opened_invariants) o
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : SteelAtomicT a opened_invariants o fp fp'

val change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelAtomicT unit opened_invariants unobservable p (fun _ -> q)

val rewrite_context (#opened:inames)
                    (#[@@@ framing_implicit] p:slprop)
                    (#[@@@ framing_implicit] q:slprop)
                    (_:unit)
  : SteelAtomicF unit opened unobservable p (fun _ -> q)
                 (requires fun _ -> p `equiv` q) (ensures fun _ _ _ -> True)

val extract_info (#opened_invariants:inames) (p:slprop) (fact:prop)
  (l:(m:mem) -> Lemma (requires interp p m) (ensures fact))
  : SteelAtomic unit opened_invariants unobservable p (fun _ -> p)
      (fun _ -> True)
      (fun _ _ _ -> fact)

val sladmit (#a:Type)
            (#opened:inames)
            (#[@@@ framing_implicit] p:pre_t)
            (#[@@@ framing_implicit] q:post_t a)
            (_:unit)
  : SteelAtomicF a opened unobservable p q (requires fun _ -> True) (ensures fun _ _ _ -> False)

val slassert (#opened_invariants:_) (p:slprop)
  : SteelAtomicT unit opened_invariants unobservable p (fun _ -> p)

val intro_pure (#opened_invariants:_) (p:prop)
  : SteelAtomic unit opened_invariants unobservable emp (fun _ -> pure p)
                (requires fun _ -> p) (ensures fun _ _ _ -> True)

val intro_exists (#a:Type) (#opened_invariants:_) (x:a) (p:a -> slprop)
  : SteelAtomicT unit opened_invariants unobservable (p x) (fun _ -> h_exists p)

val intro_exists_erased (#a:Type) (#opened_invariants:_) (x:Ghost.erased a) (p:a -> slprop)
  : SteelAtomicT unit opened_invariants unobservable (p x) (fun _ -> h_exists p)

val drop (#opened:inames) (p:slprop) : SteelAtomicT unit opened unobservable p (fun _ -> emp)

(* Witnessing an existential *)
val witness_h_exists (#a:Type) (#opened_invariants:_) (#p:a -> slprop) (_:unit)
  : SteelAtomicT (Ghost.erased a) opened_invariants unobservable
                (h_exists p) (fun x -> p x)

module U = FStar.Universe

val lift_h_exists_atomic (#a:_) (#u:_) (p:a -> slprop)
  : SteelAtomicT unit u unobservable
                (h_exists p)
                (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))

val h_exists_cong_atomic (#a:_) (#u:_) (p:a -> slprop) (q:a -> slprop {forall x. equiv (p x) (q x) })
  : SteelAtomicT unit u unobservable
                (h_exists p)
                (fun _ -> h_exists q)

val elim_pure (#uses:_) (p:prop)
  : SteelAtomicT (_:unit{p}) uses unobservable
                (pure p)
                (fun _ -> emp)

let lift_lemma #uses (p:slprop) (q:prop) (l:(hmem p -> Lemma q))
  : SteelAtomicT (u:unit{q}) uses unobservable p (fun _ -> p)
  = change_slprop p (p `star` pure q) (fun m -> l m; Steel.Memory.pure_star_interp p q m; Steel.Memory.emp_unit p);
    elim_pure q
