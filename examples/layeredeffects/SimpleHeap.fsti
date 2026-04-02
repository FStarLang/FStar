(*
   A simple heap model for use in layered effect examples.

   References are nats, the heap maps nats to typed values.
   No preorders, no witness/recall.
*)
module SimpleHeap

module S = FStar.Set
module F = FStar.FunctionalExtensionality

(** The heap type *)
val heap : Type u#1

(** References are abstract, parametric in their stored type *)
val ref ([@@@ strictly_positive] a:Type0) : Type0

(** References support decidable equality *)
val ref_equal : #a:Type0 -> #b:Type0 -> ref a -> ref b -> GTot bool

(** The address of a reference *)
val addr_of : #a:Type0 -> ref a -> GTot nat

(** addr_of is injective on same-typed refs *)
val addr_of_injective : #a:Type0 -> r1:ref a -> r2:ref a ->
  Lemma (addr_of r1 == addr_of r2 <==> r1 == r2)

(** ref_equal matches addr_of *)
val ref_equal_addr : #a:Type0 -> #b:Type0 -> r1:ref a -> r2:ref b ->
  Lemma (ref_equal r1 r2 <==> addr_of r1 = addr_of r2)

(** Whether a ref is contained (allocated) in a heap *)
val contains : #a:Type0 -> heap -> ref a -> Type0

(** Whether an address is unused in a heap *)
val addr_unused_in : nat -> heap -> Type0

(** A ref is unused iff its addr is unused *)
val unused_in : #a:Type0 -> ref a -> heap -> Type0

let fresh (#a:Type0) (r:ref a) (h0 h1:heap) =
  r `unused_in` h0 /\ h1 `contains` r

(** Select: requires the ref is contained *)
val sel : #a:Type0 -> h:heap -> r:ref a -> Ghost a (requires (h `contains` r)) (ensures fun _ -> True)

(** Update: requires the ref is contained *)
val upd : #a:Type0 -> h:heap -> r:ref a -> a -> Ghost heap (requires (h `contains` r)) (ensures fun _ -> True)

(** Allocate a fresh ref *)
val alloc : #a:Type0 -> heap -> a -> Tot (ref a & heap)

(** The next fresh address *)
val next_addr : heap -> GTot nat

(** Convenience set operations *)
let only (#a:Type0) (x:ref a) : GTot (S.set nat) = S.singleton (addr_of x)

(** The heap where both heaps agree outside a set of addresses *)
let modifies (s:S.set nat) (h0 h1:heap) =
  (forall (a:Type0) (r:ref a).
    h0 `contains` r /\ ~(S.mem (addr_of r) s) ==>
    h1 `contains` r /\ sel h0 r == sel h1 r) /\
  (forall (n:nat). addr_unused_in n h0 /\ ~(S.mem n s) ==> addr_unused_in n h1)

let equal_dom (h0 h1:heap) =
  (forall (a:Type0) (r:ref a). h0 `contains` r <==> h1 `contains` r) /\
  (forall (n:nat). addr_unused_in n h0 <==> addr_unused_in n h1)

(** ---- Axioms / Lemmas ---- *)

(** contains is stable under upd *)
val contains_upd : #a:Type0 -> #b:Type0 -> h:heap -> r:ref a -> x:a -> r':ref b ->
  Lemma (requires (h `contains` r))
        (ensures (upd h r x `contains` r' <==> h `contains` r'))

(** sel/upd laws *)
val sel_upd_same : #a:Type0 -> h:heap -> r:ref a -> x:a ->
  Lemma (requires (h `contains` r))
        (ensures (let h' = upd h r x in h' `contains` r /\ sel h' r == x))

val sel_upd_other : #a:Type0 -> #b:Type0 -> h:heap -> r1:ref a -> x:a -> r2:ref b ->
  Lemma (requires (h `contains` r1 /\ h `contains` r2 /\ addr_of r1 =!= addr_of r2))
        (ensures (let h' = upd h r1 x in h' `contains` r2 /\ sel h' r2 == sel h r2))

(** alloc produces a fresh ref *)
val alloc_fresh : #a:Type0 -> h:heap -> x:a ->
  Lemma (let (r, h1) = alloc h x in
         r `unused_in` h /\
         h1 `contains` r /\
         sel h1 r == x /\
         next_addr h1 > next_addr h /\
         (forall (b:Type0) (r':ref b). h `contains` r' ==> h1 `contains` r' /\ sel h1 r' == sel h r'))

(** alloc preserves existing refs *)
val alloc_contains : #a:Type0 -> #b:Type0 -> h:heap -> x:a -> r:ref b ->
  Lemma (requires (h `contains` r))
        (ensures (let (_, h1) = alloc h x in
                  h1 `contains` r /\ sel h1 r == sel h r))

(** unused_in and contains are disjoint *)
val unused_not_contains : #a:Type0 -> h:heap -> r:ref a ->
  Lemma (r `unused_in` h ==> ~(h `contains` r))

val contains_not_unused : #a:Type0 -> h:heap -> r:ref a ->
  Lemma (h `contains` r ==> ~(r `unused_in` h))
