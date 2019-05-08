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

abstract noeq type heap_rec = {
  next_addr: nat;
  memory   : F.restricted_t nat (fun _ -> option (a:Type0 & a))
}

abstract type heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

(* Consistency of heaps. aka, no strong updates *)
private abstract let consistent (h0:heap) (h1:heap) =
  forall n x y. h0.memory n == Some x /\ h1.memory n == Some y ==> dfst x == dfst y

(* References. *)
(* address * initial value *)
(* TODO: test that hasEq for ref is not exported *)
abstract noeq type ref (a:Type0) = {
  addr: nat;
  init: a
}

abstract val addr_of: #a:Type -> ref a -> Tot nat
let addr_of #a r = r.addr

abstract val compare_addrs: #a:Type -> #b:Type -> r1:ref a -> r2:ref b -> Tot (b:bool{b = (addr_of r1 = addr_of r2)})
let compare_addrs #a #b r1 r2 = r1.addr = r2.addr

abstract let contains_a_well_typed (#a:Type0) (h:heap) (r:ref a) =
  Some? (h.memory r.addr) /\ dfst (Some?.v (h.memory r.addr)) == a
  (* exists (x:a). h.memory r.addr == Some (| a, x |) *)

(* Select. *)
abstract val sel_tot : #a:Type -> h:heap -> r:ref a{h `contains_a_well_typed` r} -> Tot a
let sel_tot #a h r =
  match h.memory r.addr with
  | Some (| _ , x |) -> x

abstract val sel: #a:Type -> h:heap -> r:ref a -> GTot a
let sel #a h r =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains_a_well_typed` r) then
    sel_tot #a h r
  else r.init

(* Update. *)
abstract val upd_tot : #a:Type -> h0:heap -> r:ref a{h0 `contains_a_well_typed` r} -> x:a
                       -> Tot heap
let upd_tot #a h0 r x =
  { h0 with memory = F.on_dom nat (fun r' -> if r.addr = r'
			                then Some (| a, x |)
                                        else h0.memory r') }

abstract val upd: #a:Type -> h0:heap -> r:ref a -> x:a
                  -> GTot heap
let upd #a h0 r x =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h0 `contains_a_well_typed` r)
  then upd_tot h0 r x
  else
    if r.addr >= h0.next_addr
    then (* alloc at r.addr *)
      { next_addr = r.addr + 1;
        memory    = F.on_dom nat (fun (r':nat) -> if r' = r.addr
			                    then Some (| a, x |)
                                            else h0.memory r') }
    else (* type modifying update at r.addr *)
      { h0 with memory = F.on_dom nat (fun r' -> if r' = r.addr
				             then Some (| a, x |)
                                             else h0.memory r') }

(* Generating a fresh reference for the given heap. *)

abstract val alloc: #a:Type -> h0:heap -> x:a -> Tot (t:(ref a * heap){snd t == upd h0 (fst t) x})
let alloc #a h0 x =
  let r = { addr = h0.next_addr; init = x } in
  let h1 = { next_addr = r.addr + 1;
             memory    = F.on_dom nat (fun (r':nat) -> if r' = r.addr
			                         then Some (| a, x |)
                                                 else h0.memory r') }
  in
  assert (let h2 = upd h0 r x in
          FStar.FunctionalExtensionality.feq h1.memory h2.memory);
  r, h1

abstract let contains (#a:Type) (h:heap) (r:ref a): Tot Type0 = Some? (h.memory r.addr)

val contains_a_well_typed_implies_contains: #a:Type -> h:heap -> r:ref a
                              -> Lemma (requires (h `contains_a_well_typed` r))
			              (ensures  (h `contains` r))
				[SMTPatOr [[SMTPat (h `contains_a_well_typed` r)]; [SMTPat (h `contains` r)]]]
let contains_a_well_typed_implies_contains #a h r = ()

val contains_addr_of: #a:Type -> #b:Type -> h:heap -> r1:ref a -> r2:ref b
                     -> Lemma (requires (h `contains` r1 /\ ~ (h `contains` r2)))
		             (ensures  (addr_of r1 <> addr_of r2))
		       [SMTPat (h `contains` r1); SMTPat (h `contains` r2)]
let contains_addr_of #a #b h r1 r2 = ()

let fresh (s:set nat) (h0:heap) (h1:heap) =
  forall (a:Type) (r:ref a).{:pattern (h0 `contains` r)}
                       mem (addr_of r) s ==> ~ (h0 `contains` r) /\ (h1 `contains` r)

let only x = singleton (addr_of x)

val alloc_lemma: #a:Type -> h0:heap -> x:a
                 -> Lemma (requires (True))
		         (ensures (let r, h1 = alloc h0 x in
			           h1 == upd h0 r x /\ ~ (h0 `contains` r) /\ h1 `contains_a_well_typed` r))
		   [SMTPat (alloc h0 x)]
let alloc_lemma #a h0 x = ()

let sel_same_addr_of (#a:Type) (x:ref a) (y:ref a) (h:heap)
  :Lemma (requires (addr_of x = addr_of y /\ h `contains_a_well_typed` x /\ h `contains_a_well_typed` y))
         (ensures  (sel h x == sel h y))
   [SMTPat (sel h x); SMTPat (sel h y)]
  = ()

val sel_upd1: #a:Type -> h:heap -> r:ref a -> v:a -> r':ref a
	      -> Lemma (requires (addr_of r = addr_of r')) (ensures (sel (upd h r v) r' == v))
                [SMTPat (sel (upd h r v) r')]
let sel_upd1 #a h r v r' = ()

val sel_upd2: #a:Type -> #b:Type -> h:heap -> k1:ref a -> k2:ref b -> v:b
              -> Lemma (requires True) (ensures (addr_of k1 <> addr_of k2 ==> sel (upd h k2 v) k1 == sel h k1))
	        [SMTPat (sel (upd h k2 v) k1)]
let sel_upd2 #a #b h k1 k2 v = ()

val upd_sel : #a:Type -> h:heap -> r:ref a ->
	      Lemma (requires (h `contains_a_well_typed` r))
	            (ensures  (upd h r (sel h r) == h))
	      [SMTPat (upd h r (sel h r))]
let upd_sel #a h r =
  assert (FStar.FunctionalExtensionality.feq (upd h r (sel h r)).memory h.memory)

(* AR: does not need to be abstract *)
let equal_dom (h1:heap) (h2:heap) :Tot Type0 =
  forall (a:Type0) (r:ref a). h1 `contains` r <==> h2 `contains` r

(* Empty. *)
abstract val emp : heap
let emp = {
  next_addr = 0;
  memory    = F.on_dom nat (fun (r:nat) -> None)
}

val in_dom_emp: #a:Type -> k:ref a
                -> Lemma (requires True) (ensures (~ (emp `contains` k)))
		  [SMTPat (emp `contains` k)]
let in_dom_emp #a k = ()

val upd_contains: #a:Type -> #b:Type -> h:heap -> r:ref a -> v:a -> r':ref b
                  -> Lemma (requires True)
		          (ensures ((upd h r v) `contains_a_well_typed`  r /\
			            (h `contains` r' ==> (upd h r v) `contains` r')))
		    [SMTPat ((upd h r v) `contains` r')]
let upd_contains #a #b h r v r' = ()

val upd_contains_a_well_typed: #a:Type -> #b:Type -> h:heap -> r:ref a -> v:a -> r':ref b
                  -> Lemma (requires True)
		          (ensures ((upd h r v) `contains_a_well_typed` r /\
			            (((h `contains_a_well_typed` r \/ ~ (h `contains` r)) /\ h `contains_a_well_typed` r')
				     ==> (upd h r v) `contains_a_well_typed` r')))
		    [SMTPat ((upd h r v) `contains_a_well_typed` r')]
let upd_contains_a_well_typed #a #b h r v r' = ()

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

abstract val lemma_modifies_trans: m1:heap -> m2:heap -> m3:heap
                       -> s1:set nat -> s2:set nat
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                               (ensures (modifies (union s1 s2) m1 m3))
let lemma_modifies_trans m1 m2 m3 s1 s2 = ()

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
let lemma_sel_tot_is_sel_if_contains_a_well_typed #a h r = ()

val lemma_upd_tot_is_upd_if_contains_a_well_typed:
  #a:Type -> h:heap -> r:ref a{h `contains_a_well_typed` r} -> x:a
  -> Lemma (requires True)
          (ensures  (upd h r x == upd_tot h r x))
    [SMTPat (upd_tot h r x)]
let lemma_upd_tot_is_upd_if_contains_a_well_typed #a h r x = ()

val op_Hat_Plus_Plus: #a:Type -> r:ref a -> set nat -> Tot (set nat)
let op_Hat_Plus_Plus #a r s = union (only r) s

val op_Plus_Plus_Hat: #a:Type -> set nat -> r:ref a -> Tot (set nat)
let op_Plus_Plus_Hat #a s r = union s (only r)

val op_Hat_Plus_Hat: #a:Type -> #b:Type -> ref a -> ref b -> Tot (set nat)
let op_Hat_Plus_Hat #a #b r1 r2 = union (only r1) (only r2)
