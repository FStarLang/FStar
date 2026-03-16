(*
   Copyright 2024 Microsoft Research

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

module PulseCore.MemoryAlt
open FStar.Ghost
open FStar.PCM
module CM = FStar.Algebra.CommMonoid
module B = PulseCore.BaseHeapSig

let ghost_action_preorder (_:unit)
: Lemma (FStar.Preorder.preorder_rel is_ghost_action)
= B.is_ghost_action_preorder ()
 
(**** Separation logic *)

let equiv (p1 p2:slprop u#a) : prop = p1 == p2

(**
  An extensional equivalence principle for slprop
 *)

let slprop_extensionality (p q:slprop u#a)
: Lemma
    (requires p `equiv` q)
    (ensures p == q)
= ()

let slprop_equiv_refl (p:slprop)
: Lemma (p `equiv` p)
        [SMTPat (equiv p p)]
= ()
          
(** A memory maps a [ref]erence to its associated value *)
let core_ref : Type u#0 = PulseCore.Heap2.core_ref

(** [null] is a specific reference, that is not associated to any value
*)
let core_ref_null : core_ref = PulseCore.Heap2.core_ref_null

let core_ref_is_null (r:core_ref)
: b:bool { b <==> r == core_ref_null }
= PulseCore.Heap2.core_ref_is_null r

(***** Properties of separation logic equivalence *)
let emp_unit (p:slprop)
: Lemma (p `equiv` (p `star` emp))
= B.emp_unit p

#push-options "--print_implicits --print_universes"

let pure_equiv (p q:prop)
: Lemma ((p <==> q) ==> (pure u#a p `equiv` pure u#a q))
= FStar.PropositionalExtensionality.apply p q

let pure_true_emp (_:unit)
: Lemma (pure u#a True `equiv` emp)
= B.pure_true_emp u#(a+3) ()

(***** Properties of the separating conjunction *)
let star_commutative (p1 p2:slprop)
: Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))
= B.star_commutative p1 p2

let star_associative (p1 p2 p3:slprop)
: Lemma ((p1 `star` (p2 `star` p3))
          `equiv`
          ((p1 `star` p2) `star` p3))
= B.star_associative p1 p2 p3

let star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))
= ()

let full_mem_pred: mem -> prop = B.full_mem_pred 

let coerce_action_back
    (#a:Type u#x)
    (#mg:bool)
    (#pre':slprop u#a)
    (#post':a -> slprop u#a)
    (pre:B.slprop)
    (post:a -> GTot (B.slprop))
    (_:squash (pre == reveal pre' /\ (forall x. post x == reveal (post' x))))
    ($act:_pst_action_except a mg pre' post')
: B._action_except a mg pre post
= fun frame m0 -> act frame m0 

(* Some generic actions and combinators *)

let lift_ghost
      (#a:Type)
      #p #q
      (ni_a:non_info a)
      (f:erased (pst_ghost_action_except a p q))
: pst_ghost_action_except a p q
= B.lift_ghost #_ #(p) #(fun x -> q x) ni_a
    (coerce_action_back _ _ () f)

(* Concrete references *)
let pts_to = B.pts_to u#(a+3)
let split_action = B.share u#(a+3)
let gather_action = B.gather u#(a+3)
let alloc_action = B.extend u#(a+3)
let select_refine = B.read u#(a+3)
let upd_gen = B.write u#(a+3)
let pts_to_not_null_action = B.pts_to_not_null_action u#(a+3)

(* Ghost references *)
[@@erasable]
let core_ghost_ref : Type0 = B.core_ghost_ref
let core_ghost_ref_null = PulseCore.Heap2.core_ghost_ref_null
let ghost_pts_to = B.ghost_pts_to u#(a+3)
let ghost_alloc = B.ghost_extend u#(a+3)
let ghost_read = B.ghost_read u#(a+3)
let ghost_write = B.ghost_write u#(a+3)
let ghost_share = B.ghost_share u#(a+3)
let ghost_gather = B.ghost_gather u#(a+3)
let ghost_pts_to_not_null_action #a #pcm = B.ghost_pts_to_not_null_action u#(a+3) #a #pcm