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
module LowStar.RST.Array

open FStar.HyperStack.ST
module A = LowStar.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions
module MG = FStar.ModifiesGen

open LowStar.Resource
open LowStar.RST

include LowStar.RST.Array.Views

val index (#a:Type) (b:A.array a) (i:UInt32.t)
  : RST a (array_resource b)
          (fun _ -> array_resource b)
          (fun h0 -> UInt32.v i < A.vlength b)
          (fun h0 x h1 ->
          UInt32.v i < A.vlength b /\
          Seq.index (sel (array_view b) h0).s (UInt32.v i) == x /\
          sel (array_view b) h0 == sel (array_view b) h1
          )

val upd (#a:Type) (b:A.array a) (i:UInt32.t) (v:a)
  : RST unit (array_resource b)
             (fun _ -> array_resource b)
             (fun h0 -> UInt32.v i < A.vlength b /\ P.allows_write (sel (array_view b) h0).p )
             (fun h0 _ h1 -> UInt32.v i < A.vlength b /\
             (sel (array_view b) h1).s ==
             Seq.upd (sel (array_view b) h0).s (UInt32.v i) v /\
             (sel (array_view b) h1).p == (sel (array_view b) h0).p
             )

val alloc (#a:Type) (init:a) (len:UInt32.t)
  : RST (A.array a)
        (empty_resource)
        (fun b -> full_array_resource b)
        (fun _ -> UInt32.v len > 0)
        (fun _ b h1 ->
        (sel (full_array_view b) h1).s == Seq.create (UInt32.v len) init /\
        (sel (full_array_view b) h1).p = FStar.Real.one
        )

val free (#a:Type) (b:A.array a)
  : RST unit (full_array_resource b)
             (fun _ -> empty_resource)
             (fun h0 -> P.allows_write (sel (full_array_view b) h0).p)
             (fun _ _ _ -> True)

val share (#a:Type) (b:A.array a)
  : RST (A.array a)
        (array_resource b)
        (fun b' -> array_resource b <*> array_resource b')
        (fun h0 -> A.vlength b > 0)
        (fun h0 b' h1 ->
          (sel (array_view b) h0).s == (sel (array_view b) h1).s /\
          (sel (array_view b') h1).s == (sel (array_view b) h1).s /\
          (sel (array_view b) h1).p == P.half_permission (sel (array_view b) h0).p /\
          (sel (array_view b') h1).p == P.half_permission (sel (array_view b) h0).p /\
          summable_permissions h1 b b')

val merge (#a:Type) (b b':A.array a)
  : RST unit (array_resource b <*> array_resource b')
             (fun _ -> array_resource b)
             (fun h0 -> A.mergeable b b' /\ summable_permissions h0 b b')
             (fun h0 _ h1 ->
               summable_permissions h0 b b' /\
               (sel (array_view b) h0).s == (sel (array_view b) h1).s /\
               (sel (array_view b) h1).p == P.sum_permissions (sel (array_view b) h0).p (sel (array_view b') h0).p)


val split (#a: Type) (b: A.array a) (idx: UInt32.t{UInt32.v idx > 0 /\ UInt32.v idx < A.vlength b})
  : RST (A.array a & A.array a)
    (array_resource b)
    (fun p -> array_resource (fst p) <*> array_resource (snd p))
    (fun _ -> True)
    (fun h0 (b1, b2) h1 ->
      A.is_split_into b (b1, b2) /\
      (sel (array_view b1) h1).s == Seq.slice (sel (array_view b) h0).s 0 (UInt32.v idx) /\
      (sel (array_view b2) h1).s == Seq.slice (sel (array_view b) h0).s (UInt32.v idx) (A.vlength b) /\
      (sel (array_view b) h0).p == (sel (array_view b1) h1).p /\
      (sel (array_view b) h0).p == (sel (array_view b2) h1).p
    )

val glue (#a: Type) (b b1 b2: A.array a)
  : RST unit
    (array_resource b1 <*> array_resource b2)
    (fun _ -> array_resource b)
    (fun h0 -> A.is_split_into b (b1, b2) /\  (sel (array_view b1) h0).p == (sel (array_view b2) h0).p)
    (fun h0 _ h1 ->
      (sel (array_view b) h1).s == Seq.append (sel (array_view b1) h0).s (sel (array_view b2) h0).s /\
      (sel (array_view b) h1).p == (sel (array_view b1) h0).p
    )


let frame_delta_pre_full (#a:Type) (b:A.array a) (outer0 inner0 delta0:resource) =
  outer0 `can_be_split_into` (full_array_resource b, delta0) /\
  inner0 `can_be_split_into` (array_resource b, delta0)

let frame_delta_post_full (#t:Type) (#a:Type) (b:A.array a) (outer1 inner1 delta1:t -> resource) =
  forall x. (
    (outer1 x) `can_be_split_into` (full_array_resource b, delta1 x) /\
    (inner1 x) `can_be_split_into` (array_resource b, delta1 x))

unfold
let frame_full_pre (#a:Type) (b:A.array a) (outer0 inner0:resource)
  (delta0:resource{frame_delta_pre_full b outer0 inner0 delta0})
  (pre:r_pre inner0)
  (h:imem (inv outer0))
  =
  reveal_full_array();
  reveal_array();
  reveal_can_be_split_into();
  sel (array_view b) h == sel (full_array_view b) h ==> pre h
  
unfold
let frame_full_post(#t:Type)
                   (#a:Type)
                   (b:A.array a)
                   (outer0 inner0:resource)                   
                   (delta0:resource{frame_delta_pre_full b outer0 inner0 delta0})
                   (outer1 inner1:t -> resource)
                   (delta1:t -> resource{frame_delta_post_full b outer1 inner1 delta1})
                   (post:r_post inner0 t inner1)
                   (h0:imem (inv outer0))
                   (x:t)
                   (h1:imem (inv (outer1 x)))
    = reveal_array();
      reveal_full_array();
      reveal_can_be_split_into();
      post h0 x h1 /\
      sel (array_view b) h0 == sel (full_array_view b) h0 /\
      sel (array_view b) h1 == sel (full_array_view b) h1

open LowStar.RST.Tactics

open FStar.Algebra.CommMonoid.Equiv
open FStar.Tactics
open FStar.Tactics.CanonCommMonoidSimple.Equiv


val frame_full_array (#t:Type) (#a:Type) (b:A.array a)
    (outer0:resource)
    (outer1:t -> resource)
    (#inner0:resource)
    (#inner1:t -> resource)
    (#[(fun () -> tadmit()
          // refine_intro();
          // dump "refine_intro";
          // flip();
          // apply_lemma (`unfold_with_tactic);
          // dump "hello";
          // norm [delta_only [`%frame_delta_pre_full]];
          // split(); apply_lemma (quote can_be_split_into_star); canon_monoid req rm; apply_lemma (quote can_be_split_into_star); canon_monoid req rm
    ) ()]
      delta0:resource{FStar.Tactics.with_tactic
                     (fun () -> tadmit())
                     // split(); apply_lemma (quote can_be_split_into_star); canon_monoid req rm; apply_lemma (quote can_be_split_into_star); canon_monoid req rm)
                     (frame_delta_pre_full b outer0 inner0 delta0)
                     // (outer0 `can_be_split_into` (full_array_resource b, delta0) /\
                     // inner0 `can_be_split_into` (array_resource b, delta0))
                     })
    (#
      delta1:(t -> resource){FStar.Tactics.with_tactic
                     (fun () -> tadmit ())
                     (forall x. (outer1 x) `can_be_split_into` (full_array_resource b, delta1 x)) /\
                     (forall x. (inner1 x) `can_be_split_into` (array_resource b, delta1 x))
                     })    
    (#pre:r_pre inner0)
    (#post:r_post inner0 t inner1)
    ($f:unit -> RST t inner0 inner1 pre post)
    : RST t
      outer0
      outer1
      (FStar.Tactics.by_tactic_seman _ (fun () -> tadmit()) (frame_delta_pre_full b outer0 inner0 delta0);
        frame_full_pre b outer0 inner0 delta0 pre)
      (frame_full_post b outer0 inner0 delta0 outer1 inner1 delta1 post)


#reset-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.qi.eager_threshold=1000"
#restart-solver
let read_write_without_sharing () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let b = alloc 2ul 42ul in
  let h0 = HST.get() in
  let x = frame_full_array #unit #_ b (full_array_resource b) (fun _ -> full_array_resource b) #_ #_
    #(empty_resource) #(fun _ -> empty_resource)
    (fun () ->
      upd b 0ul 0ul
    ) in
  let h1 = HST.get() in
  free b
