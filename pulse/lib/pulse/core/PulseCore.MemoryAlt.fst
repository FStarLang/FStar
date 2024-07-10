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
module PST = PulseCore.HoareStateMonad
module U = FStar.Universe
module S = FStar.Set
module CM = FStar.Algebra.CommMonoid
module H = PulseCore.HeapSig
module E = PulseCore.HeapExtension
module B = PulseCore.BaseHeapSig
/// This module adds memory invariants to the heap to expose the
/// final interface for Pulse's PCM-based memory model.

(* Signatures, numbers by their offset from the top-levl signature, sig.
   Should make it somewhat easier to add a level *)
let sig_3 : H.heap_sig u#a = B.base_heap u#a
let sig_2 : H.heap_sig u#(a + 1) = E.extend (sig_3 u#a)
let sig_1 : H.heap_sig u#(a + 2) = E.extend sig_2
let sig : H.heap_sig u#(a + 3) = E.extend sig_1
(** Abstract type of memories *)
let mem  : Type u#(a + 4) = sig.mem

let is_ghost_action (m0 m1:mem u#a) : prop = sig.is_ghost_action m0 m1

let ghost_action_preorder (_:unit)
: Lemma (FStar.Preorder.preorder_rel is_ghost_action)
= sig.is_ghost_action_preorder ()
 
(**** Separation logic *)

(** The type of separation logic propositions. Based on Steel.Heap.slprop *)
let slprop : Type u#(a + 4) = erased sig.slprop
let reveal_slprop (p:slprop) : sig.slprop = sig.non_info_slprop p

let slprop3_base : Type u#(a + 3) = erased sig.bprop
let cm_slprop3 : CM.cm slprop3_base = H.cm_e_slprop sig_1
let down3 (s:slprop u#a) : slprop3_base u#a = sig.down s
let up3 (s:slprop3_base u#a) : slprop u#a = reveal_slprop <| sig.up s
let up3_is_slprop3_alt (b:slprop3_base)
: Lemma (is_slprop3 (up3 b))
        [SMTPat (is_slprop3 (up3 b))]
= sig.up_down b
let up3_is_slprop3 (b:slprop3_base) : Lemma (is_slprop3 (up3 b)) = ()

let slprop2_base : Type u#(a + 2) = erased sig_1.bprop
let cm_slprop2 : CM.cm slprop2_base = H.cm_e_slprop sig_2
let down2 (s:slprop u#a) : slprop2_base u#a = sig_1.down (sig.down s)
let up2 (s:slprop2_base u#a) : slprop u#a = reveal_slprop <| sig.up (sig_1.up s)
let up2_down2 (s:slprop2_base)
: Lemma (down2 (up2 s) == s)
= calc (==) {
    down2 (up2 s);
  (==) {}
    down2 (sig.up (sig_1.up s));
  (==) {}
    hide <| sig_1.down (sig.down (sig.up (sig_1.up s)));
  (==) { sig.up_down (sig_1.up s) }
    hide <| sig_1.down (sig_1.up s);
  (==) { sig_1.up_down s }
    s;
  }
let up2_is_slprop2_alt (s:slprop2_base)
: Lemma (ensures is_slprop2 (up2 s))
        [SMTPat (is_slprop2 (up2 s))]
= up2_down2 s
let up2_is_slprop2 s = up2_is_slprop2_alt s

let slprop_2_is_3 (s:slprop)
: Lemma (is_slprop2 s ==> is_slprop3 s)
= sig.up_down (sig_1.up (sig_1.down (down3 s)))


let slprop1_base : Type u#(a + 1) = erased sig_2.bprop
let cm_slprop1 : CM.cm slprop1_base = H.cm_e_slprop sig_3
let down1 (s:slprop u#a) : slprop1_base u#a = sig_2.down (down2 s)
let up1 (s:slprop1_base u#a) : slprop u#a = reveal_slprop <| up2 (sig_2.up s)
let up1_down1 (s:slprop1_base)
: Lemma (down1 (up1 s) == s)
= calc (==) {
    down1 (up1 s);
  (==) {}
    hide <| sig_2.down (down2 (up2 (sig_2.up s)));
  (==) { up2_down2 (sig_2.up s) }
    hide <| sig_2.down (sig_2.up s);
  (==) { sig_2.up_down s }
    s;
  }
let up1_is_slprop1_alt (s:slprop1_base)
: Lemma (ensures is_slprop1 (up1 s))
        [SMTPat (is_slprop1 (up1 s))]
= up1_down1 s
let up1_is_slprop1 s = up1_is_slprop1_alt s

let slprop_1_is_2 (s:slprop)
: Lemma (is_slprop1 s ==> is_slprop2 s)
= sig_1.up_down (sig_2.up (sig_2.down (down2 s)))

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


let emp_is_slprop2 () 
: Lemma (is_slprop2 sig.emp)
= E.up_emp sig_2;
  E.up_emp sig_1;
  sig_1.up_down sig_2.emp;
  sig.up_down sig_1.emp

let pure_is_slprop2 (p:prop) 
: Lemma (is_slprop2 (sig.pure p))
= E.up_pure sig_2 p;
  E.up_pure sig_1 p;
  sig_1.up_down (sig_2.pure p);
  sig.up_down (sig_1.pure p)

let emp
: slprop u#a
= emp_is_slprop2(); sig.emp

let pure (p:prop)
: slprop2 u#a
= pure_is_slprop2 p; sig.pure p

let star  (p1 p2:slprop u#a)
: slprop u#a
= sig.star p1 p2

module F = FStar.FunctionalExtensionality
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
= sig.star_commutative p1 p2

let star_associative (p1 p2 p3:slprop)
: Lemma ((p1 `star` (p2 `star` p3))
          `equiv`
          ((p1 `star` p2) `star` p3))
= sig.star_associative p1 p2 p3

let star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))
= ()

let slprop3_star_congruence (p1 p2:slprop3 u#a)
: Lemma (is_slprop3 (p1 `star` p2))
= sig.star_congruence p1 p2

module T = FStar.Tactics.V2
let slprop3_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
: Lemma
  (requires forall x. is_slprop3 (p x))
  (ensures is_slprop3 (h_exists p))
= introduce forall x. is_slprop3 (reveal_slprop (p x))
  with (  
    assert (is_slprop3 (p x))  
  );
  assert (H.is_boxable (H.exists_ #sig #a (fun x -> reveal_slprop (p x))))
    by (T.mapply (`E.exists_congruence))

let slprop2_star_congruence (p1 p2:slprop2 u#a)
: Lemma (is_slprop2 (p1 `star` p2))
= calc (==) {
    reveal_slprop <| up2 (down2 (p1 `star` p2));
  (==) {}
    sig.up (sig_1.up (sig_1.down (sig.down (p1 `star` p2))));
  (==) { E.down_star p1 p2 }
    sig.up (sig_1.up (sig_1.down (down3 p1 `sig_1.star` down3 p2)));
  (==) { E.down_star #sig_2 (down3 p1) (down3 p2) }
    sig.up (sig_1.up (down2 p1 `sig_2.star` down2 p2));
  (==) { E.up_star #sig_2 (down2 p1) (down2 p2) }
    sig.up (sig_1.up (down2 p1) `sig_1.star` (sig_1.up (down2 p2)));
  (==) { E.up_star #sig_1 (sig_1.up (down2 p1)) (sig_1.up (down2 p2)) }
    sig.up (sig_1.up (down2 p1)) `sig.star` sig.up (sig_1.up (down2 p2));
  (==) { (*def*) }
    sig.up (sig_1.up (sig_1.down (sig.down p1)))
    `sig.star`
    sig.up (sig_1.up (sig_1.down (sig.down p2)));
  (==) { E.up_star #sig_1 (sig_1.up (down2 p1)) (sig_1.up (down2 p2)) }
    reveal_slprop (p1 `star` p2);
  }

let reveal_bprop (x:slprop3_base) : sig_1.slprop = sig_1.non_info_slprop x

let down_exists_alt #a (p: a -> slprop)
: Lemma 
  (ensures down3 (h_exists p) ==
           hide <| H.exists_ #sig_1 (fun x -> sig_1.non_info_slprop <| down3 (p x)))
= calc (==) {
    reveal_bprop (down3 (h_exists p));
  (==) {}
    sig.down (H.exists_ (fun x -> reveal_slprop (p x)));
  (==) { _ by (T.mapply (`E.down_exists)) }
    H.exists_ #sig_1 (fun x -> sig.down (reveal_slprop (p x)));
  (==) { H.exists_extensionality #sig_1
          (fun x -> sig.down (reveal_slprop (p x)))
          (fun x -> sig_1.non_info_slprop <| down3 (p x)) }
    H.exists_ #sig_1 (fun x -> sig_1.non_info_slprop <| down3 (p x));
  } 


let split_small (p:slprop u#a)
: Lemma (requires is_slprop2 p)
        (ensures H.is_boxable #sig_1 (sig_1.non_info_slprop (down3 p)))
= calc (==) {
   hide <| sig_1.up (sig_1.down (down3 p));
  (==) {  sig.up_down (sig_1.up (sig_1.down (down3 p))) }
   down3 (up3 (sig_1.up (sig_1.down (down3 p))));
  (==) { }
   down3 (up2 (down2 p));
  (==) {}
   down3 p;
  }

let slprop2_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
: Lemma
  (requires forall x. is_slprop2 (p x))
  (ensures is_slprop2 (h_exists p))
= FStar.Classical.forall_intro slprop_2_is_3;
  slprop3_exists_congruence #a p;
  assert (is_slprop3 (h_exists p));
  down_exists_alt #a p;
  assert (forall x. H.is_boxable #sig_1 (sig_1.non_info_slprop (down3 (p x))))
      by (let _ = T.forall_intro () in
          T.mapply (`split_small));
  assert (H.is_boxable #sig_1
           (H.exists_ #sig_1 (fun x -> sig_1.non_info_slprop <| down3 (p x))))
     by (T.mapply (`E.exists_congruence))
     
let h_exists_equiv (#a:Type) (p q : a -> slprop)
: Lemma
    (requires (forall x. p x `equiv` q x))
    (ensures (h_exists p == h_exists q))
= calc (==) {
    reveal_slprop <| h_exists p;
  (==) {}
    H.exists_ #sig #a (fun x -> reveal_slprop (p x));
  // (==) { _ by (T.mapply (`H.exists_extensionality)) } //this fails
  (==) { H.exists_extensionality #sig #a (fun x -> reveal_slprop (p x)) (fun x -> reveal_slprop (q x)) }
    H.exists_ #sig #a (fun x -> reveal_slprop (q x));
  (==) {}
    reveal_slprop <| h_exists q;
  }

let up3_emp ()
: Lemma (up3 cm_slprop3.unit == emp)
= E.up_emp sig_1
let down3_emp ()
: Lemma (down3 emp == cm_slprop3.unit)
= E.down_emp sig_1
let up3_star  (p q:slprop3_base)
: Lemma (up3 (p `cm_slprop3.mult` q) == up3 p `star` up3 q)
= E.up_star #sig_1 p q
let down3_star (p q:slprop)
: Lemma (down3 (p `star` q) == down3 p `cm_slprop3.mult` down3 q)
= E.down_star #sig_1 p q

let up2_emp ()
: Lemma (up2 cm_slprop2.unit == emp)
= E.up_emp sig_2;
  E.up_emp sig_1
let down2_emp ()
: Lemma (down2 emp == cm_slprop2.unit)
= E.down_emp sig_2;
  E.down_emp sig_1
let up2_star (p q:slprop2_base)
: Lemma (up2 (p `cm_slprop2.mult` q) == up2 p `star` up2 q)
= calc (==) {
    reveal_slprop <| up2 (p `cm_slprop2.mult` q);
  == {}
    sig.up (sig_1.up (p `sig_2.star` q));
  == { E.up_star #sig_2 p q }
    sig.up (sig_1.up p `sig_1.star` sig_1.up q);
  == { E.up_star #sig_1 (sig_1.up p) (sig_1.up q) }
    reveal_slprop <| up2 p `star` up2 q;
  }

let reveal_slprop2 (b:slprop2_base) : sig_2.slprop = sig_2.non_info_slprop b
let down2_star (p q:slprop)
: Lemma (down2 (p `star` q) == down2 p `cm_slprop2.mult` down2 q)
= calc (==) {
    reveal_slprop2 <| down2 (p `star` q);
  == {}
    sig_1.down (sig.down (p `star` q));
  == { E.down_star #sig_1 p q }
    sig_1.down ((down3 p) `sig_1.star` (down3 q));
  == { E.down_star #sig_2 (down3 p) (down3 q) }
    reveal_slprop2 <| down2 p `sig_2.star` down2 q;
  }

let slprop1_star_congruence (p1 p2:slprop1 u#a)
: Lemma (is_slprop1 (p1 `star` p2))
= calc (==) {
    up1 (down1 (p1 `star` p2));
  (==) {}
    up2 (sig_2.up (sig_2.down (down2 (p1 `star` p2))));
  (==) { down2_star p1 p2 }
    up2 (sig_2.up (sig_2.down (down2 p1 `sig_2.star` down2 p2)));
  (==) { E.down_star #sig_3 (down2 p1) (down2 p2) }
    up2 (sig_2.up (down1 p1 `sig_3.star` down1 p2));
  (==) { E.up_star #sig_3 (down1 p1) (down1 p2) }
    up2 (sig_2.up (down1 p1) `sig_2.star` (sig_2.up (down1 p2)));
  (==)  { up2_star (sig_2.up (down1 p1)) (sig_2.up (down1 p2)) }
   up1 (down1 p1) `star` up1 (down1 p2);
  (==) {}
   p1 `star` p2;
  }

let down_exists_sig2 a (p: a -> GTot sig_1.slprop)
  : Lemma 
    (ensures sig_1.down (H.exists_ #sig_1 p) ==
             H.exists_ #sig_2 (fun x -> sig_1.down (p x)))
  = calc (==) {
      sig_1.down (H.exists_ #sig_1 p);
    (==) {}
      (E.extend sig_2).down (H.exists_ #(E.extend sig_2) p);
    (==) { E.down_exists #sig_2 #a p }
      H.exists_ #sig_2 (fun x -> (E.extend sig_2).down (p x));
    (==) { _ by (T.trefl ()) }
      H.exists_ #sig_2 (fun x -> sig_1.down (p x));
  }

let down_exists_alt2 #a (p: a -> slprop)
: Lemma 
  (ensures down2 (h_exists p) ==
           hide <| H.exists_ #sig_2 (fun x -> sig_2.non_info_slprop <| down2 (p x)))
= 
  calc (==) {
    reveal (down2 (h_exists p));
  (==) {}
    sig_1.down (down3 (h_exists p));
  (==) { down_exists_alt p }
    sig_1.down (H.exists_ #sig_1 #a (fun x -> sig_1.non_info_slprop (down3 (p x))));
  (==) { down_exists_sig2 a (fun x -> sig_1.non_info_slprop (down3 (p x))) }
    H.exists_ #sig_2 (fun x -> sig_1.down (sig_1.non_info_slprop (down3 (p x))));
  (==) { H.exists_extensionality #sig_2
          (fun x -> sig_1.down (sig_1.non_info_slprop (down3 (p x))))
          (fun x -> sig_2.non_info_slprop <| down2 (p x)) }
    H.exists_ #sig_2 (fun x -> sig_2.non_info_slprop <| down2 (p x));
  }


let split_small1 (p:slprop u#a)
: Lemma (requires is_slprop1 p)
        (ensures H.is_boxable #sig_2 (sig_2.non_info_slprop (down2 p)))
= calc (==) {
   sig_2.up (sig_2.down (down2 p));
  (==) { sig_1.up_down (sig_2.up (sig_2.down (down2 p))) }
   sig_1.down (sig_1.up (sig_2.up (sig_2.down (down2 p))));
  (==) {}
   sig_1.down (sig_1.up (sig_2.up (down1 p)));
  (==) { sig.up_down (sig_1.up (sig_2.up (down1 p))) }
    sig_1.down (sig.down (sig.up (sig_1.up (sig_2.up (down1 p)))));
  (==) {}
    sig_1.down (sig.down (up1 (down1 p)));
  (==) {}
   reveal <| down2 p;
  }

let slprop1_exists_congruence (#a:Type u#a) (p:a -> slprop u#b)
  : Lemma
    (requires forall x. is_slprop1 (p x))
    (ensures is_slprop1 (h_exists p))
= FStar.Classical.forall_intro slprop_1_is_2;
  slprop2_exists_congruence #a p;
  assert (is_slprop2 (h_exists p));
  down_exists_alt2 #a p;
  assert (forall x. H.is_boxable #sig_2 (sig_2.non_info_slprop (down2 (p x))))
      by (let _ = T.forall_intro () in
          T.mapply (`split_small1));
  assert (H.is_boxable #sig_2
           (H.exists_ #sig_2 (fun x -> sig_2.non_info_slprop <| down2 (p x))))
     by (T.mapply (`E.exists_congruence))
     
(**** Memory invariants *)
let iref : Type0 = erased sig.iref
let injective_iref (i:iref) = E.injective_invariant i
let storable_iref (i:iref) = E.storable_invariant i
let deq_iref : FStar.GhostSet.decide_eq iref = fun x y -> sig.deq_iref x y
let down_inames (e:inames)
: GhostSet.set sig.iref
= GhostSet.comprehend (fun (i:sig.iref) -> GhostSet.mem (hide i) e)
let inames_ok (e:inames) (m:mem) : prop = H.inames_ok (down_inames e) m

(** The empty set of invariants is always empty *)
let inames_ok_empty (m:mem)
: Lemma (ensures inames_ok GhostSet.empty m)
        [SMTPat (inames_ok GhostSet.empty m)]
= ()

(**
  This separation logic proposition asserts that all the invariants whose names are in [e]
  are in effect and satisfied on the heap inside the memory [m]
*)
let mem_invariant (e:inames) (m:mem u#a)
: slprop u#a
= sig.mem_invariant (down_inames e) m

let full_mem_pred: mem -> prop = sig.full_mem_pred 

let reveal_iref (i:iref) : sig.iref = 
  let x : erased (sig.iref) = hide (reveal i) in
  sig.non_info_iref x

let inv (i:iref) (p:slprop u#a) : slprop u#a = sig.inv (reveal_iref i) p

let storable_inv (i:iref { storable_iref i }) (p:slprop { is_slprop3 p })
: Lemma (is_slprop3 (inv i p))
= E.storable_inv _ i p

let coerce_action
    (#a:Type u#x)
    (#mg:bool)
    (#ex:inames)
    (#pre:sig.slprop)
    (#post:a -> GTot (sig.slprop))
    (#pre':slprop u#a)
    (#post':a -> slprop u#a)
    (_:squash (pre == reveal pre' /\ (forall x. post x == reveal (post' x))))
    ($act:H._action_except (sig u#a) a mg (down_inames ex) pre post)
: _pst_action_except a mg ex pre' post'
= fun frame m0 -> act (reveal_slprop frame) m0 

let coerce_action_back
    (#a:Type u#x)
    (#mg:bool)
    (#ex:inames)
    (#pre':slprop u#a)
    (#post':a -> slprop u#a)
    (pre:sig.slprop)
    (post:a -> GTot (sig.slprop))
    (_:squash (pre == reveal pre' /\ (forall x. post x == reveal (post' x))))
    ($act:_pst_action_except a mg ex pre' post')
: H._action_except (sig u#a) a mg (down_inames ex) pre post
= fun frame m0 -> act frame m0 

let dup_inv (e:inames) (i:iref) (p:slprop u#a)
: pst_ghost_action_except unit e 
    (inv i p) 
    (fun _ -> inv i p `star` inv i p)
= coerce_action () <| E.dup_inv #(sig_1 u#a) (down_inames e) (reveal_iref i) (reveal_slprop p)


let new_invariant (e:inames) (p:slprop { is_slprop3 p })
: pst_ghost_action_except (i:iref{injective_iref i}) e
    p
    (fun i -> inv i p)
= fun frame m0 -> 
    let i, m1 = E.new_invariant #(sig_1 u#a) (down_inames e) (reveal_slprop p) (reveal_slprop frame) m0 in
    hide i, m1

let slprop2_boxable (p:slprop{ is_slprop2 p})
: Lemma (H.is_boxable #sig_1 (down3 p))
        [SMTPat (is_slprop2 p)]
= calc (==) {
    sig_1.up (sig_1.down (down3 p));
  (==) { sig.up_down (sig_1.up (sig_1.down (sig.down p))) }
    sig.down (sig.up (sig_1.up (sig_1.down (sig.down p))));
  (==) { sig.up_down (sig_1.up (sig_1.down (sig.down p))) }
    sig.down (up2 (down2 p));
  (==) {}
    reveal <| sig.down p;  
  }


let lift_inv (i:E.iiref sig_2) (p:slprop { is_slprop2 p })
: Lemma (sig.up (sig_1.inv i (down3 p)) == reveal_slprop <| inv (E.lift_iref #sig_1 i) p)
        [SMTPat (sig.up (sig_1.inv i (down3 p)))]
= E.lift_inv sig_1 i (down3 p)

let new_storable_invariant_alt (e:inames) (p:slprop u#a { is_slprop2 p })
: pst_ghost_action_except (E.iiref (sig_2 u#a)) e 
    p
    (fun i -> inv (E.lift_iref #sig_1 i) p)
= coerce_action () <|
  E.lift_action_alt #sig_1 <|
  E.new_invariant #(sig_2 u#a)
      (E.lower_inames #(sig_1 u#a) (down_inames e))
      (sig_1.non_info_slprop (down3 p))

let new_storable_invariant (e:inames) (p:slprop { is_slprop2 p })
: pst_ghost_action_except (i:iref{storable_iref i}) e 
    p
    (fun i -> inv i p)
= fun frame m0 ->
    let i,m1 = new_storable_invariant_alt e p frame m0 in
    E.lift_iref_is_storable #sig_1 i;
    hide <| E.lift_iref #sig_1 i, m1

let with_invariant_alt
    (#h:H.heap_sig u#a)
    (#a:Type u#aa)
    (#fp:(E.extend h).slprop)
    (#fp':(a -> (E.extend h).slprop))
    (#opened_invariants:H.inames (E.extend h))
    (#p:(E.extend h).slprop)
    (#maybe_ghost:bool)
    (i:(E.extend h).iref{not (GhostSet.mem i opened_invariants)})
    ($f:H._action_except (E.extend h) a maybe_ghost
      (HeapSig.add_iref i opened_invariants)
      (p `(E.extend h).star` fp)
      (fun x -> p `(E.extend h).star` fp' x))
: H._action_except (E.extend h) a maybe_ghost opened_invariants 
      ((E.extend h).inv i p `(E.extend h).star` fp)
      (fun x -> (E.extend h).inv i p `(E.extend h).star` fp' x)
= E.with_invariant #h #a #fp #fp' #opened_invariants #p #maybe_ghost i f

let with_invariant (#a:Type u#x)
                   (#fp:slprop u#a)
                   (#fp':a -> slprop u#a)
                   (#opened_invariants:inames)
                   (#p:slprop u#a)
                   (#maybe_ghost:bool)
                   (i:iref{not (mem_inv opened_invariants i)})
                   (f:_pst_action_except a maybe_ghost
                        (add_inv opened_invariants i) 
                        (p `star` fp)
                        (fun x -> p `star` fp' x))
: _pst_action_except a maybe_ghost opened_invariants 
      (inv i p `star` fp)
      (fun x -> inv i p `star` fp' x)
= assume (injective_iref i);
  assert (GhostSet.equal
    (down_inames (add_inv opened_invariants i))
    (H.add_iref (reveal_iref i) (down_inames opened_invariants)));
  coerce_action () <|
  with_invariant_alt 
    #(sig_1 u#a) #a
    #(reveal_slprop fp) 
    #(fun x -> reveal_slprop (fp' x)) 
    #(down_inames opened_invariants)
    #(reveal_slprop p) #maybe_ghost
    (reveal_iref i)
    (coerce_action_back _ (fun x -> p `star` reveal_slprop (fp' x)) () f)

let lift_action_alt
    (#h:H.heap_sig u#h)
    (#a:Type u#a)
    (#mg:bool)
    (#ex:H.inames (E.extend h))
    (#pre:erased h.slprop)
    (#post:a -> GTot h.slprop)
    (action:H._action_except h a mg (E.lower_inames ex) pre post)
: H._action_except (E.extend h)
    a mg ex 
    ((E.extend h).up pre)
    (fun x -> (E.extend h).up (post x))
= E.lift_action_alt #h #a #mg #ex #(h.non_info_slprop pre) #post action

#push-options "--print_implicits"
let distinct_invariants_have_distinct_names_alt
      (e:inames)
      (p:slprop u#m)
      (q:slprop u#m { p =!= q })
      (i:iref { injective_iref i }) (j:iref { injective_iref j })
: pst_ghost_action_except u#0 u#m 
    (squash (~(eq2 #(E.iiref sig_1) (reveal_iref i) (reveal_iref j))))
    e 
    (inv i p `star` inv j q)
    (fun _ -> inv i p `star` inv j q)
= coerce_action 
    #_ 
    #_
    #_
    #_
    #_
    #(inv i p `star` inv j q)
    #(fun _ -> inv i p `star` inv j q)
     () <|
  E.distinct_invariants_have_distinct_names 
    #(sig_1 u#m) 
    (down_inames e) (reveal_slprop p) (reveal_slprop q) (reveal_iref i) (reveal_iref j)

let distinct_invariants_have_distinct_names
      (e:inames)
      (p:slprop u#m)
      (q:slprop u#m { p =!= q })
      (i:iref { injective_iref i }) (j:iref { injective_iref j })
: pst_ghost_action_except u#0 u#m 
    (squash (i =!= j))
    e 
    (inv i p `star` inv j q)
    (fun _ -> inv i p `star` inv j q)
= fun frame m0 -> let x, y = distinct_invariants_have_distinct_names_alt e p q i j frame m0 in x, y

let invariant_name_identifies_invariant_alt
      (e:inames)
      (p q:slprop u#m)
      (i:iref)
      (j:iref { i == j /\ injective_iref j } )
: pst_ghost_action_except (squash (reveal_slprop p == reveal_slprop q)) e
   (inv i p `star` inv j q)
   (fun _ -> inv i p `star` inv j q)
= coerce_action 
    #(squash (reveal_slprop p == reveal_slprop q))
    #_
    #_
    #_
    #_
    #(inv i p `star` inv j q)
    #(fun _ -> inv i p `star` inv j q)
     () <|
  E.invariant_name_identifies_invariant #(sig_1 u#m) (down_inames e) (reveal_slprop p) (reveal_slprop q) (reveal_iref i) (reveal_iref j)

let invariant_name_identifies_invariant
      (e:inames)
      (p q:slprop u#m)
      (i:iref)
      (j:iref { i == j /\ injective_iref j } )
: pst_ghost_action_except (squash (p == q)) e
   (inv i p `star` inv j q)
   (fun _ -> inv i p `star` inv j q)
= fun frame m0 -> 
    let x, m1 = invariant_name_identifies_invariant_alt e p q i j frame m0 in
    (), m1

let rec coerce_ctx (ctx:erased (list iref))
: erased (list sig.iref)
= match reveal ctx with
  | [] -> []
  | hd::tl -> hide (reveal hd :: coerce_ctx tl)

let rec coerce_ctx_mem (ctx:erased (list iref))
: Lemma (forall (i:E.iiref sig_1). List.Tot.memP i (coerce_ctx ctx) <==> List.Tot.memP (hide i) ctx)
= match ctx with
  | [] -> ()
  | hd::tl -> 
    let _ = coerce_ctx_mem tl in
    ()

let fresh_invariant_alt (e:inames) (p:slprop3 u#m) (ctx:erased (list iref))
: pst_ghost_action_except (i:E.iiref sig_1 { E.fresh_wrt (coerce_ctx ctx) i }) e
       p
       (fun i -> inv i p)
= coerce_action 
    #(i:E.iiref sig_1 { E.fresh_wrt (coerce_ctx ctx) i})
    #_
    #_
    #(reveal_slprop p)
    #(fun i -> sig.inv i (reveal_slprop p))
    #p
    #(fun i -> inv i p)
  () <|
  E.fresh_invariant #(sig_1 u#m) (down_inames e) (reveal_slprop p) (coerce_ctx ctx)

let fresh_invariant (e:inames) (p:slprop3 u#m) (ctx:erased (list iref))
: pst_ghost_action_except (i:iref { fresh_wrt ctx i }) e
       p
       (fun i -> inv i p)
= fun frame m0 -> 
    let x, m1 = fresh_invariant_alt e p ctx frame m0 in
    coerce_ctx_mem ctx;
    hide x, m1

(* Some generic actions and combinators *)

let pst_frame
      (#a:Type)
      (#maybe_ghost:bool)
      (#opened_invariants:inames)
      (#pre:slprop)
      (#post:a -> slprop)
      (frame:slprop)
      ($f:_pst_action_except a maybe_ghost opened_invariants pre post)
: _pst_action_except a maybe_ghost opened_invariants (pre `star` frame) (fun x -> post x `star` frame)
= coerce_action () <|
  HeapSig.frame #_ #_ #_ #_
      #(reveal_slprop pre)
      #(fun x -> post x)
      (reveal_slprop frame)
      (coerce_action_back _ _ () f)

let witness_h_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
: pst_ghost_action_except (erased a) opened_invariants
           (h_exists p)
           (fun x -> p x)
= calc (==) {
    reveal (h_exists p);
  (==) {}
    reveal (H.exists_ (fun x -> reveal_slprop (p x)));
  (==) { H.exists_extensionality (fun x -> reveal (p x)) (fun x -> reveal_slprop (p x)) }
    H.exists_ (fun x -> reveal (p x));
  };
  coerce_action () <|
  HeapSig.witness_exists #_ #_ #_ (fun x -> p x)


let intro_exists (#opened_invariants:_) (#a:_) (p:a -> slprop) (x:erased a)
: pst_ghost_action_except unit opened_invariants
      (p x)
      (fun _ -> h_exists p)
= coerce_action () <|
  HeapSig.intro_exists #_ #_ #_ (fun x -> reveal_slprop (p x)) x

let lift_h_exists (#opened_invariants:_) (#a:Type u#a) (p:a -> slprop u#m)
  : pst_ghost_action_except unit opened_invariants
           (h_exists p)
           (fun _a -> h_exists #(U.raise_t u#a u#b a) (U.lift_dom p))
 = calc (==) {
    reveal_slprop <| h_exists #(U.raise_t u#a u#b a) (U.lift_dom p);
  (==) { _ by (T.trefl()) }
    reveal_slprop <| hide <| HeapSig.exists_ #sig #(U.raise_t u#a u#b a) (fun x -> reveal_slprop (U.lift_dom p x));
  (==) {}
    HeapSig.exists_ #sig #(U.raise_t u#a u#b a) (fun x -> reveal_slprop (U.lift_dom p x));
  (==) { H.exists_extensionality #sig
            (fun x -> reveal_slprop (U.lift_dom p x))
            (HeapSig.lift_dom_ghost (fun x -> reveal_slprop (p x))) }
    HeapSig.exists_ #sig #(U.raise_t u#a u#b a) (HeapSig.lift_dom_ghost (fun x -> reveal_slprop (p x)));
   }; 
   coerce_action () <|
   HeapSig.lift_h_exists #_ #_ #_ (fun x -> reveal_slprop (p x))


let elim_pure (#opened_invariants:_) (p:prop)
: pst_ghost_action_except (u:unit{p}) opened_invariants (pure p) (fun _ -> emp)
= coerce_action () <|
  HeapSig.elim_pure #_ #_ p

let intro_pure (#opened_invariants:_) (p:prop) (x:squash p)
: pst_ghost_action_except unit opened_invariants emp (fun _ -> pure p)
= coerce_action () <|
  HeapSig.intro_pure #_ #_ p x
  
let drop (#opened_invariants:_) (p:slprop)
: pst_ghost_action_except unit opened_invariants p (fun _ -> emp)
= coerce_action () <|
  HeapSig.drop #_ #_ (reveal_slprop p)

let lift_ghost
      (#a:Type)
      #opened_invariants #p #q
      (ni_a:non_info a)
      (f:erased (pst_ghost_action_except a opened_invariants p q))
: pst_ghost_action_except a opened_invariants p q
= coerce_action () <|
  HeapSig.lift_ghost #_ #_ #_ #(reveal_slprop p) #(fun x -> q x) ni_a
    (coerce_action_back _ _ () f)

(* Concrete references to "small" types *)
let pts_to (#a:Type u#(a + 1)) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a
 = up2 (E.pts_to #sig_3 #a #pcm r v)

let wrap (#h:H.heap_sig u#a) (p:erased h.slprop) : h.slprop = h.non_info_slprop p


// let coerce_action_alt
//     (#a:Type u#x)
//     (#mg:bool)
//     (#ex:inames)
//     (#pre:erased (slprop u#a))
//     (#post:a -> GTot (slprop u#a))
//     (#pre':erased (slprop u#a))
//     (#post':a -> GTot (slprop u#a))
//     (_:squash (pre == pre' /\ (forall x. post x == post' x)))
//     ($act:_pst_action_except a mg ex pre post)
// : _pst_action_except a mg ex pre' post'
// = act

(** Splitting a permission on a composite resource into two separate permissions *)
let split_action
  (#a:Type u#(a + 1))
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e 
     (pts_to r (v0 `op pcm` v1))
     (fun _ -> pts_to r v0 `star` pts_to r v1)
= up2_star (E.pts_to #sig_3 #a #pcm r v0) (E.pts_to #sig_3 #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (pts_to r (v0 `op pcm` v1))) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.split_action #sig_3 #a #pcm (E.lower_inames #(sig_2) (E.lower_inames #(sig_1 u#a) (down_inames e))) r v0 v1
  

(** Combining separate permissions into a single composite permission*)
let gather_action
  (#a:Type u#(a + 1))
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1)) e
    (pts_to r v0 `star` pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))
= up2_star (E.pts_to #sig_3 #a #pcm r v0) (E.pts_to #sig_3 #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (pts_to r v0 `star` pts_to r v1)) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.gather_action #sig_3 #a #pcm
      (E.lower_inames #sig_2 (E.lower_inames #(sig_1 u#a) (down_inames e)))
      r v0 v1

let alloc_action (#a:Type u#(a+1)) (#pcm:pcm a) (e:inames) (x:a{pcm.refine x})
: pst_action_except (ref a pcm) e
    emp
    (fun r -> pts_to r x)
= up2_emp ();
  coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> up2 (E.pts_to #sig_3 #a #pcm r x)) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.alloc_action #sig_3 #a #pcm
          (E.lower_inames #sig_2 (E.lower_inames #(sig_1 u#a) (down_inames e)))
          x

let select_refine (#a:Type u#(a+1)) (#p:pcm a)
                  (e:inames)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v}) e
    (pts_to r x)
    (fun v -> pts_to r (f v))
= coerce_action #(v:a{compatible p x v /\ p.refine v}) #_ #_ #(reveal_slprop (pts_to r x)) 
                #(fun v -> up2 (E.pts_to #sig_3 #a #p r (f v))) #(pts_to r x) #(fun v -> pts_to r (f v)) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.select_refine #sig_3 #a #p 
                  (E.lower_inames #sig_2 (E.lower_inames #(sig_1 u#a) (down_inames e)))
                  r x f

let upd_gen (#a:Type u#(a+1)) (#p:pcm a) (e:inames) (r:ref a p) (x y:Ghost.erased a)
            (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit e
    (pts_to r x)
    (fun _ -> pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (pts_to r x)) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.upd_gen #sig_3 #a #p
            (E.lower_inames #sig_2 (E.lower_inames #(sig_1 u#a) (down_inames e))) 
            r x y f

let pts_to_not_null_action 
      (#a:Type u#(a+1)) (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (pts_to r v)
    (fun _ -> pts_to r v)
= coerce_action #_ #_ #_ #(reveal_slprop (pts_to r v)) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.pts_to_not_null_action #sig_3 #a #pcm
                 (E.lower_inames #sig_2 (E.lower_inames #(sig_1 u#a) (down_inames e)))
                 r v 


(* Ghost references to "small" types *)
[@@erasable]
let core_ghost_ref : Type0 = H.core_ghost_ref
let ghost_pts_to (#a:Type u#(a+1)) (#p:pcm a) (r:ghost_ref p) (v:a)
: slprop u#a
= up2 (E.ghost_pts_to #sig_3 #a #p r v)

let ghost_alloc
    (#e:_)
    (#a:Type u#(a+1))
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    e
    emp 
    (fun r -> ghost_pts_to r x)
= up2_emp ();
  coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> up2 (E.ghost_pts_to #sig_3 #a #pcm r x)) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.ghost_alloc #sig_3 #a #pcm
         (E.lower_inames #sig_2 (E.lower_inames #(sig_1 u#a) (down_inames e)))
          x

let ghost_read
    #e
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    e
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))
= coerce_action #(erased (v:a{compatible p x v /\ p.refine v})) #_ #_
                #(reveal_slprop (ghost_pts_to r x)) 
                #(fun v -> up2 (E.ghost_pts_to #sig_3 #a #p r (f v)))
                #(ghost_pts_to r x)
                #(fun v -> ghost_pts_to r (f v))
                () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.ghost_read #sig_3 #a #p
               (E.lower_inames (E.lower_inames #(sig_1 u#a) (down_inames e)))
              r x f

let ghost_write
    #e
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit e
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (ghost_pts_to r x)) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.ghost_write #sig_3 #a #p
                (E.lower_inames #sig_2 (E.lower_inames #(sig_1 u#a) (down_inames e))) 
                r x y f


let ghost_share
    #e
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 `star` ghost_pts_to r v1)
= up2_star (E.ghost_pts_to #sig_3 #a #pcm r v0) (E.ghost_pts_to #sig_3 #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (ghost_pts_to r (v0 `op pcm` v1))) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.ghost_share #sig_3 #a #pcm 
                (E.lower_inames #sig_2 (E.lower_inames #(sig_1 u#a) (down_inames e)))
                r v0 v1


let ghost_gather
    #e
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1)) e
    (ghost_pts_to r v0 `star` ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))
= up2_star (E.ghost_pts_to #sig_3 #a #pcm r v0) (E.ghost_pts_to #sig_3 #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (ghost_pts_to r v0 `star` ghost_pts_to r v1)) () <|
  lift_action_alt #sig_1 <|
  lift_action_alt #sig_2 <|
  E.ghost_gather #sig_3 #a #pcm
                 (E.lower_inames (E.lower_inames #(sig_1 u#a) (down_inames e)))
                 r v0 v1


(* Concrete references to "big" types *)
let big_pts_to (#a:Type u#(a + 2)) (#pcm:_) (r:ref a pcm) (v:a)
: slprop3 u#a
= up3 (E.pts_to #sig_2 #a #pcm r v)

(** Splitting a permission on a composite resource into two separate permissions *)
let big_split_action
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (big_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_pts_to r v0 `star` big_pts_to r v1)
= up3_star (E.pts_to #sig_2 #a #pcm r v0) (E.pts_to #sig_2 #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (big_pts_to r (v0 `op pcm` v1))) () <|
  lift_action_alt #sig_1 <|
  E.split_action #sig_2 #_ #pcm (E.lower_inames #(sig_1 u#a) (down_inames e)) r v0 v1

let big_gather_action
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1)) e
    (big_pts_to r v0 `star` big_pts_to r v1)
    (fun _ -> big_pts_to r (op pcm v0 v1))
= up3_star (E.pts_to #sig_2 #a #pcm r v0) (E.pts_to #sig_2 #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (big_pts_to r v0 `star` big_pts_to r v1)) () <|
  lift_action_alt #sig_1 <|
  E.gather_action #sig_2 #_ #pcm (E.lower_inames #(sig_1 u#a) (down_inames e)) r v0 v1

let big_alloc_action
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (e:inames)
      (x:a{pcm.refine x})
: pst_action_except (ref a pcm) e
    emp
    (fun r -> big_pts_to r x)
= up3_emp ();
  coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> up3 (E.pts_to #sig_2 #a #pcm r x)) () <|
  lift_action_alt #sig_1 <|
  E.alloc_action #sig_2 #_ #pcm (E.lower_inames #(sig_1 u#a) (down_inames e)) x

let big_select_refine
      (#a:Type u#(a + 2))
      (#p:pcm a)
      (e:inames)
      (r:ref a p)
      (x:erased a)
      (f:(v:a{compatible p x v}
          -> GTot (y:a{compatible p y v /\
                      FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v}) e
    (big_pts_to r x)
    (fun v -> big_pts_to r (f v))
= coerce_action #(v:a{compatible p x v /\ p.refine v}) #_ #_
      #(reveal_slprop (big_pts_to r x))
      #(fun v -> up3 (E.pts_to #sig_2 #a #p r (f v)))
      #(big_pts_to r x)
      #(fun v -> big_pts_to r (f v))
      () <|
  lift_action_alt #sig_1 <|
  E.select_refine #sig_2 #_ #p (E.lower_inames #(sig_1 u#a) (down_inames e)) r x f

let big_upd_gen
    (#a:Type u#(a + 2))
    (#p:pcm a)
    (e:inames)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit e
    (big_pts_to r x)
    (fun _ -> big_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (big_pts_to r x)) () <|
  lift_action_alt #sig_1 <|
  E.upd_gen #sig_2 #_ #p (E.lower_inames #(sig_1 u#a) (down_inames e)) r x y f

let big_pts_to_not_null_action 
      (#a:Type u#(a + 2))
      (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (big_pts_to r v)
    (fun _ -> big_pts_to r v)
= coerce_action #_ #_ #_ #(reveal_slprop (big_pts_to r v)) () <|
  lift_action_alt #sig_1 <|
  E.pts_to_not_null_action #sig_2 #_ #pcm (E.lower_inames #(sig_1 u#a) (down_inames e)) r v

(* Ghost references to "big" types *)
let big_ghost_pts_to (#a:Type u#(a + 2)) (#p:pcm a) (r:ghost_ref p) (v:a)
: slprop3 u#a
= up3 (E.ghost_pts_to #sig_2 #a #p r v)

let big_ghost_alloc
    (#o:_)
    (#a:Type u#(a + 2))
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    o
    emp 
    (fun r -> big_ghost_pts_to r x)
= up3_emp ();
  coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> up3 (E.ghost_pts_to #sig_2 #a #pcm r x)) () <|
  lift_action_alt #sig_1 <|
  E.ghost_alloc #sig_2 #_ #pcm (E.lower_inames #(sig_1 u#a) (down_inames o)) x

let big_ghost_read
    #o
    (#a:Type u#(a + 2))
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    o
    (big_ghost_pts_to r x)
    (fun v -> big_ghost_pts_to r (f v))
= coerce_action #(erased (v:a{compatible p x v /\ p.refine v})) #_ #_
                #(reveal_slprop (big_ghost_pts_to r x)) 
                #(fun v -> up3 (E.ghost_pts_to #sig_2 #a #p r (f v)))
                #(big_ghost_pts_to r x)
                #(fun v -> big_ghost_pts_to r (f v))
                () <|
  lift_action_alt #sig_1 <|
  E.ghost_read #sig_2 #_ #p (E.lower_inames #(sig_1 u#a) (down_inames o)) r x f

let big_ghost_write
    #o
    (#a:Type u#(a + 2))
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit o 
    (big_ghost_pts_to r x)
    (fun _ -> big_ghost_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (big_ghost_pts_to r x)) () <|
  lift_action_alt #sig_1 <|
  E.ghost_write #sig_2 #_ #p (E.lower_inames #(sig_1 u#a) (down_inames o)) r x y f

let big_ghost_share
    #e
    (#a:Type u#(a + 2))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (big_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)
= up3_star (E.ghost_pts_to #sig_2 #a #pcm r v0) (E.ghost_pts_to #sig_2 #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (big_ghost_pts_to r (v0 `op pcm` v1))) () <|
  lift_action_alt #sig_1 <|
  E.ghost_share #sig_2 #_ #pcm (E.lower_inames #(sig_1 u#a) (down_inames e)) r v0 v1


let big_ghost_gather
    #e
    (#a:Type u#(a + 2))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1)) e
    (big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)
    (fun _ -> big_ghost_pts_to r (op pcm v0 v1))
= up3_star (E.ghost_pts_to #sig_2 #a #pcm r v0) (E.ghost_pts_to #sig_2 #a #pcm r v1);
  coerce_action #_ #_ #_ #(reveal_slprop (big_ghost_pts_to r v0 `star` big_ghost_pts_to r v1)) () <|
  lift_action_alt #sig_1 <|
  E.ghost_gather #sig_2 #_ #pcm (E.lower_inames #(sig_1 u#a) (down_inames e)) r v0 v1

  (* References for objects in universes a+3, "non-boxable" pts_to *)
let nb_pts_to (#a:Type u#(a + 3)) (#pcm:_) (r:ref a pcm) (v:a)
: slprop u#a
= E.pts_to #sig_1 #a #pcm r v

(** Splitting a permission on a composite resource into two separate permissions *)
let nb_split_action
      (#a:Type u#(a + 3))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit e
    (nb_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_pts_to r v0 `star` nb_pts_to r v1)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_pts_to r (v0 `op pcm` v1))) () <|
  E.split_action #sig_1 #_ #pcm (down_inames e) r v0 v1


(** Combining separate permissions into a single composite permission *)
let nb_gather_action
      (#a:Type u#(a + 3))
      (#pcm:pcm a)
      (e:inames)
      (r:ref a pcm)
      (v0:FStar.Ghost.erased a)
      (v1:FStar.Ghost.erased a)
: pst_ghost_action_except (squash (composable pcm v0 v1)) e
    (nb_pts_to r v0 `star` nb_pts_to r v1)
    (fun _ -> nb_pts_to r (op pcm v0 v1))
= coerce_action #_ #_ #_ #(reveal_slprop (nb_pts_to r v0 `star` nb_pts_to r v1)) () <|
  E.gather_action #sig_1 #_ #pcm (down_inames e) r v0 v1

let nb_alloc_action
      (#a:Type u#(a + 3))
      (#pcm:pcm a)
      (e:inames)
      (x:a{pcm.refine x})
: pst_action_except (ref a pcm) e
    emp
    (fun r -> nb_pts_to r x)
= coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> E.pts_to #sig_1 #a #pcm r x) () <|
  E.alloc_action #sig_1 #_ #pcm (down_inames e) x


let nb_select_refine
      (#a:Type u#(a + 3))
      (#p:pcm a)
      (e:inames)
      (r:ref a p)
      (x:erased a)
      (f:(v:a{compatible p x v}
          -> GTot (y:a{compatible p y v /\
                      FStar.PCM.frame_compatible p x v y})))
: pst_action_except (v:a{compatible p x v /\ p.refine v}) e
    (nb_pts_to r x)
    (fun v -> nb_pts_to r (f v))
= coerce_action #(v:a{compatible p x v /\ p.refine v}) #_ #_
      #(reveal_slprop (nb_pts_to r x))
      #(fun v -> nb_pts_to #a #p r (f v))
      #(nb_pts_to r x)
      #(fun v -> nb_pts_to r (f v))
      () <|
  E.select_refine #sig_1 #_ #p (down_inames e) r x f

let nb_upd_gen
    (#a:Type u#(a + 3))
    (#p:pcm a)
    (e:inames)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_action_except unit e
    (nb_pts_to r x)
    (fun _ -> nb_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_pts_to r x)) () <|
  E.upd_gen #sig_1 #_ #p (down_inames e) r x y f


let nb_pts_to_not_null_action 
      (#a:Type u#(a + 3))
      (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (nb_pts_to r v)
    (fun _ -> nb_pts_to r v)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_pts_to r v)) () <|
  E.pts_to_not_null_action #sig_1 #_ #pcm (down_inames e) r v

let nb_ghost_pts_to (#a:Type u#(a + 3)) (#p:pcm a) (r:ghost_ref p) (v:a)
: slprop u#a
= E.ghost_pts_to #sig_1 #a #p r v

let nb_ghost_alloc
    (#o:_)
    (#a:Type u#(a + 3))
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    o
    emp 
    (fun r -> nb_ghost_pts_to r x)
= coerce_action #_ #_ #_ #(reveal_slprop emp) #(fun r -> E.ghost_pts_to #sig_1 #a #pcm r x) () <|
  E.ghost_alloc #sig_1 #_ #pcm (down_inames o) x

let nb_ghost_read
    #o
    (#a:Type u#(a + 3))
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    o
    (nb_ghost_pts_to r x)
    (fun v -> nb_ghost_pts_to r (f v))
= coerce_action #(erased (v:a{compatible p x v /\ p.refine v})) #_ #_
                #(reveal_slprop (nb_ghost_pts_to r x)) 
                #(fun v -> (E.ghost_pts_to #sig_1 #a #p r (f v)))
                #(nb_ghost_pts_to r x)
                #(fun v -> nb_ghost_pts_to r (f v))
                () <|
  E.ghost_read #sig_1 #_ #p (down_inames o) r x f


let nb_ghost_write
    #o
    (#a:Type u#(a + 3))
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit o 
    (nb_ghost_pts_to r x)
    (fun _ -> nb_ghost_pts_to r y)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_ghost_pts_to r x)) () <|
  E.ghost_write #sig_1 #_ #p (down_inames o) r x y f


let nb_ghost_share
    #o
    (#a:Type u#(a + 3))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit o
    (nb_ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> nb_ghost_pts_to r v0 `star` nb_ghost_pts_to r v1)
= coerce_action #_ #_ #_ #(reveal_slprop (nb_ghost_pts_to r (v0 `op pcm` v1))) () <|
  E.ghost_share #sig_1 #_ #pcm (down_inames o) r v0 v1


let nb_ghost_gather
    #o
    (#a:Type u#(a + 3))
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1)) o
    (nb_ghost_pts_to r v0 `star` nb_ghost_pts_to r v1)
    (fun _ -> nb_ghost_pts_to r (op pcm v0 v1))
= coerce_action #_ #_ #_ #(reveal_slprop (nb_ghost_pts_to r v0 `star` nb_ghost_pts_to r v1)) () <|
  E.ghost_gather #sig_1 #_ #pcm (down_inames o) r v0 v1


