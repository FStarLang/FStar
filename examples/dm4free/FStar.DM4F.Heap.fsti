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
module FStar.DM4F.Heap

open FStar.Classical
open FStar.Set

module F = FStar.FunctionalExtensionality

(* Heap is a tuple of a source of freshness (the no. of the next
   reference to be allocated) and a mapping of allocated raw
   references (represented as natural numbers) to types and values. *)

val heap : Type u#1

(* References. *)
(* address * initial value *)
(* TODO: test that hasEq for ref is not exported *)
//abstract
val ref (a:Type0) : Type0

val addr_of: #a:Type -> ref a -> Tot nat

val compare_addrs: #a:Type -> #b:Type -> r1:ref a -> r2:ref b -> Tot (b:bool{b = (addr_of r1 = addr_of r2)})

val contains_a_well_typed (#a:Type0) (h:heap) (r:ref a) : Type0

(* Select. *)
val sel_tot : #a:Type -> h:heap -> r:ref a{h `contains_a_well_typed` r} -> Tot a

val sel: #a:Type -> h:heap -> r:ref a -> GTot a

(* Update. *)
val upd_tot : #a:Type -> h0:heap -> r:ref a{h0 `contains_a_well_typed` r} -> x:a -> Tot heap

val upd: #a:Type -> h0:heap -> r:ref a -> x:a
                  -> GTot heap
(* Generating a fresh reference for the given heap. *)

val alloc: #a:Type -> h0:heap -> x:a -> Tot (t:(ref a * heap){snd t == upd h0 (fst t) x})

val contains (#a:Type) (h:heap) (r:ref a): Tot Type0

val contains_a_well_typed_implies_contains: #a:Type -> h:heap -> r:ref a
                              -> Lemma (requires (h `contains_a_well_typed` r))
			              (ensures  (h `contains` r))
				[SMTPatOr [[SMTPat (h `contains_a_well_typed` r)]; [SMTPat (h `contains` r)]]]

val contains_addr_of: #a:Type -> #b:Type -> h:heap -> r1:ref a -> r2:ref b
                     -> Lemma (requires (h `contains` r1 /\ ~ (h `contains` r2)))
		             (ensures  (addr_of r1 <> addr_of r2))
		       [SMTPat (h `contains` r1); SMTPat (h `contains` r2)]

let fresh (s:set nat) (h0:heap) (h1:heap) =
  forall (a:Type) (r:ref a).{:pattern (h0 `contains` r)}
                       mem (addr_of r) s ==> ~ (h0 `contains` r) /\ (h1 `contains` r)

let only x = singleton (addr_of x)


val alloc_lemma: #a:Type -> h0:heap -> x:a
                 -> Lemma (requires (True))
		         (ensures (let r, h1 = alloc h0 x in
			           h1 == upd h0 r x /\ ~ (h0 `contains` r) /\ h1 `contains_a_well_typed` r))
		   [SMTPat (alloc h0 x)]

val sel_same_addr_of (#a:Type) (x:ref a) (y:ref a) (h:heap)
  :Lemma (requires (addr_of x = addr_of y /\ h `contains_a_well_typed` x /\ h `contains_a_well_typed` y))
         (ensures  (sel h x == sel h y))
   [SMTPat (sel h x); SMTPat (sel h y)]

val sel_upd1: #a:Type -> h:heap -> r:ref a -> v:a -> r':ref a
	      -> Lemma (requires (addr_of r = addr_of r')) (ensures (sel (upd h r v) r' == v))
                [SMTPat (sel (upd h r v) r')]

val sel_upd2: #a:Type -> #b:Type -> h:heap -> k1:ref a -> k2:ref b -> v:b
              -> Lemma (requires True) (ensures (addr_of k1 <> addr_of k2 ==> sel (upd h k2 v) k1 == sel h k1))
	        [SMTPat (sel (upd h k2 v) k1)]

val upd_sel : #a:Type -> h:heap -> r:ref a ->
	      Lemma (requires (h `contains_a_well_typed` r))
	            (ensures  (upd h r (sel h r) == h))
	      [SMTPat (upd h r (sel h r))]

(* AR: does not need to be abstract *)
let equal_dom (h1:heap) (h2:heap) :Tot Type0 =
  forall (a:Type0) (r:ref a). h1 `contains` r <==> h2 `contains` r

(* Empty. *)
//abstract
val emp : heap

val in_dom_emp: #a:Type -> k:ref a
                -> Lemma (requires True) (ensures (~ (emp `contains` k)))
		  [SMTPat (emp `contains` k)]

val upd_contains: #a:Type -> #b:Type -> h:heap -> r:ref a -> v:a -> r':ref b
                  -> Lemma (requires True)
		          (ensures ((upd h r v) `contains_a_well_typed`  r /\
			            (h `contains` r' ==> (upd h r v) `contains` r')))
		    [SMTPat ((upd h r v) `contains` r')]

val upd_contains_a_well_typed: #a:Type -> #b:Type -> h:heap -> r:ref a -> v:a -> r':ref b
                  -> Lemma (requires True)
		          (ensures ((upd h r v) `contains_a_well_typed` r /\
			            (((h `contains_a_well_typed` r \/ ~ (h `contains` r)) /\ h `contains_a_well_typed` r')
				     ==> (upd h r v) `contains_a_well_typed` r')))
		    [SMTPat ((upd h r v) `contains_a_well_typed` r')]

let modifies (s:set nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
                         ~ (mem (addr_of r) s) /\ h0 `contains` r ==>
                         sel h1 r == sel h0 r) /\
  (forall (a:Type) (r:ref a).{:pattern (h1 `contains` r)}
                        h0 `contains` r ==> h1 `contains` r) /\
  (* AR: an alternative to this would be to prove a lemma that if sel is same and h0 contains_a_well_typed then h1 contains_a_well_typed, then the following clause would follow from the first clause of sel remaining same *)
  (forall (a:Type) (r:ref a).{:pattern (h1 `contains_a_well_typed` r)}
                        (~ (mem (addr_of r) s) /\ h0 `contains_a_well_typed` r) ==> h1 `contains_a_well_typed` r)

(* let modifies (s:set nat) (h0:heap) (h1:heap) = *)
(*   (forall (a:Type) (r:ref a).{:pattern (sel h1 r)} *)
(*                          ~ (mem (addr_of r) s) /\ h0 `contains_a_well_typed` r ==> *)
(*                          sel h1 r == sel h0 r) /\ *)
(*   (forall (a:Type) (r:ref a).{:pattern (h1 `contains_a_well_typed` r)} *)
(*                         h0 `contains_a_well_typed` r ==> h1 `contains_a_well_typed` r) *)

val lemma_modifies_trans: m1:heap -> m2:heap -> m3:heap
                       -> s1:set nat -> s2:set nat
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                               (ensures (modifies (union s1 s2) m1 m3))

(* abstract let equal (h1:heap) (h2:heap) = *)
(*   h1.next_addr = h2.next_addr /\ *)
(*   FStar.FunctionalExtensionality.feq h1.memory h2.memory *)

(* val equal_extensional: h1:heap -> h2:heap *)
(*                        -> Lemma (requires True) (ensures (equal h1 h2 <==> h1 == h2)) *)
(* 		         [SMTPat (equal h1 h2)] *)
(* let equal_extensional h1 h2 = ()			  *)

(* that sel_tot is same as sel and upd_tot is same as upd if h contains_a_well_typed r *)
val lemma_sel_tot_is_sel_if_contains_a_well_typed:
  #a:Type -> h:heap -> r:ref a{h `contains_a_well_typed` r}
  -> Lemma (requires True)
          (ensures  (sel_tot h r == sel h r))
    [SMTPat (sel_tot h r)]

val lemma_upd_tot_is_upd_if_contains_a_well_typed:
  #a:Type -> h:heap -> r:ref a{h `contains_a_well_typed` r} -> x:a
  -> Lemma (requires True)
          (ensures  (upd h r x == upd_tot h r x))
    [SMTPat (upd_tot h r x)]

let op_Hat_Plus_Plus (#a:Type) (r:ref a) (s:set nat) : Tot (set nat) =
  union (only r) s

let op_Plus_Plus_Hat (#a:Type) (s:set nat) (r:ref a): Tot (set nat) = union s (only r)

let op_Hat_Plus_Hat (#a:Type) (#b:Type) (r1:ref a) (r2:ref b) : Tot (set nat) =
  union (only r1) (only r2)
