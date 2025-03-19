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
module U = FStar.Universe
module CM = FStar.Algebra.CommMonoid
module H = PulseCore.HeapSig
module B = PulseCore.BaseHeapSig
/// This module adds memory invariants to the heap to expose the
/// final interface for Pulse's PCM-based memory model.

(* Signatures, numbers by their offset from the top-levl signature, sig.
   Should make it somewhat easier to add a level *)
let sig : H.heap_sig u#(a+3) = B.base_heap u#(a+3)
(** Abstract type of memories *)
let mem  : Type u#(a + 4) = sig.mem

let is_ghost_action (m0 m1:mem u#a) : prop = sig.is_ghost_action m0 m1

let ghost_action_preorder (_:unit)
: Lemma (FStar.Preorder.preorder_rel is_ghost_action)
= sig.is_ghost_action_preorder ()
 
(**** Separation logic *)

(** The type of separation logic propositions. Based on Steel.Heap.slprop *)
let slprop : Type u#(a + 4) = sig.slprop
let reveal_slprop (p:slprop) : sig.slprop = sig.non_info_slprop p

(** Interpreting mem assertions as memory predicates *)
let interp (p:slprop u#a) (m:mem u#a) : prop = H.interpret p m

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

let emp
: slprop u#a
= sig.emp

let pure (p:prop)
: slprop u#a
= sig.pure p

let star  (p1 p2:slprop u#a)
: slprop u#a
= sig.star p1 p2

let h_exists (#a:Type u#b) (f: (a -> slprop u#a))
: slprop u#a
= H.exists_ #sig #a (fun x -> reveal_slprop (f x))

(***** Properties of separation logic equivalence *)
let emp_unit (p:slprop)
: Lemma (p `equiv` (p `star` emp))
= sig.emp_unit p

let pure_equiv (p q:prop)
: Lemma ((p <==> q) ==> (pure p `equiv` pure q))
= FStar.PropositionalExtensionality.apply p q

let pure_true_emp (_:unit)
: Lemma (pure True `equiv` emp)
= sig.pure_true_emp ()

(***** Properties of the separating conjunction *)
let star_commutative (p1 p2:slprop)
: Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))
= HeapSig.star_commutative p1 p2

let star_associative (p1 p2 p3:slprop)
: Lemma ((p1 `star` (p2 `star` p3))
          `equiv`
          ((p1 `star` p2) `star` p3))
= HeapSig.star_associative p1 p2 p3

let star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))
= ()

let full_mem_pred: mem -> prop = sig.full_mem_pred 

let pulse_sep_sig : HeapSig.separable mem = sig.sep
let pulse_heap_sig0 : HeapSig.heap_sig u#(a + 3) = {
  mem=mem u#a;
  sep = sig.sep;
  full_mem_pred;
  is_ghost_action = sig.is_ghost_action;
  is_ghost_action_preorder = sig.is_ghost_action_preorder;
  update_ghost = sig.update_ghost;
  slprop;
  interp=(fun x -> sig.interp x); 
  as_slprop=(fun x -> sig.as_slprop x);
  interp_as=sig.interp_as;
  slprop_extensionality=(fun x y -> sig.slprop_extensionality x y);
  non_info_slprop = (fun (x:erased slprop) -> reveal x);
  emp;
  pure;
  star;
  intro_emp=sig.intro_emp;
  pure_interp=sig.pure_interp;
  pure_true_emp;
  emp_unit;
  star_equiv=(fun x y -> sig.star_equiv x y);
}
let pulse_heap_sig : hs:PulseCore.HeapSig.heap_sig u#(a + 3) {
  hs.mem == mem /\
  hs.slprop == slprop /\
  hs.emp == emp /\
  hs.star == star /\
  pure == hs.pure /\
  (forall p m. interp p m == hs.interp p m) /\
  (forall m1 m2. is_ghost_action m1 m2 == hs.is_ghost_action m1 m2) /\
  full_mem_pred == hs.full_mem_pred
}
= let hs = pulse_heap_sig0 u#a in
  hs

let coerce_action_back
    (#a:Type u#x)
    (#mg:bool)
    (#pre':slprop u#a)
    (#post':a -> slprop u#a)
    (pre:sig.slprop)
    (post:a -> GTot (sig.slprop))
    (_:squash (pre == reveal pre' /\ (forall x. post x == reveal (post' x))))
    ($act:_pst_action_except a mg pre' post')
: H._action_except (sig u#a) a mg pre post
= fun frame m0 -> act frame m0 

(* Some generic actions and combinators *)

let lift_ghost
      (#a:Type)
      #p #q
      (ni_a:non_info a)
      (f:erased (pst_ghost_action_except a p q))
: pst_ghost_action_except a p q
= HeapSig.lift_ghost #_ #_ #(reveal_slprop p) #(fun x -> q x) ni_a
    (coerce_action_back _ _ () f)

(* Concrete references to "small" types *)
let pts_to = B.pts_to' u#(a+1) u#(a+3)

let wrap (#h:H.heap_sig u#a) (p:erased h.slprop) : h.slprop = h.non_info_slprop p

let split_action = B.share' u#(a+1) u#(a+3)
let gather_action = B.gather' u#(a+1) u#(a+3)
let alloc_action = B.extend' u#(a+1) u#(a+3)
let select_refine = B.read' u#(a+1) u#(a+3)
let upd_gen = B.write' u#(a+1) u#(a+3)
let pts_to_not_null_action = B.pts_to_not_null_action' u#(a+1) u#(a+3)

(* Ghost references to "small" types *)
[@@erasable]
let core_ghost_ref : Type0 = H.core_ghost_ref
let ghost_pts_to = B.ghost_pts_to' u#(a+1) u#(a+3)
let ghost_alloc = B.ghost_extend' u#(a+1) u#(a+3)
let ghost_read = B.ghost_read' u#(a+1) u#(a+3)
let ghost_write = B.ghost_write' u#(a+1) u#(a+3)
let ghost_share = B.ghost_share' u#(a+1) u#(a+3)
let ghost_gather = B.ghost_gather' u#(a+1) u#(a+3)

(* Concrete references to "big" types *)
let big_pts_to = B.pts_to' u#(a+2) u#(a+3)
let big_split_action = B.share' u#(a+2) u#(a+3)
let big_gather_action = B.gather' u#(a+2) u#(a+3)
let big_alloc_action = B.extend' u#(a+2) u#(a+3)
let big_select_refine = B.read' u#(a+2) u#(a+3)
let big_upd_gen = B.write' u#(a+2) u#(a+3)
let big_pts_to_not_null_action = B.pts_to_not_null_action' u#(a+2) u#(a+3)

(* Ghost references to "big" types *)
let big_ghost_pts_to = B.ghost_pts_to' u#(a+2) u#(a+3)
let big_ghost_alloc = B.ghost_extend' u#(a+2) u#(a+3)
let big_ghost_read = B.ghost_read' u#(a+2) u#(a+3)
let big_ghost_write = B.ghost_write' u#(a+2) u#(a+3)
let big_ghost_share = B.ghost_share' u#(a+2) u#(a+3)
let big_ghost_gather = B.ghost_gather' u#(a+2) u#(a+3)

  (* References for objects in universes a+3, "non-boxable" pts_to *)
let nb_pts_to = B.pts_to u#(a+3)
let nb_split_action = B.share u#(a+3)
let nb_gather_action = B.gather u#(a+3)
let nb_alloc_action = B.extend u#(a+3)
let nb_select_refine = B.read u#(a+3)
let nb_upd_gen = B.write u#(a+3)
let nb_pts_to_not_null_action = B.pts_to_not_null_action u#(a+3)

let nb_ghost_pts_to = B.ghost_pts_to u#(a+3)
let nb_ghost_alloc = B.ghost_extend u#(a+3)
let nb_ghost_read = B.ghost_read u#(a+3)
let nb_ghost_write = B.ghost_write u#(a+3)
let nb_ghost_share = B.ghost_share u#(a+3)
let nb_ghost_gather = B.ghost_gather u#(a+3)