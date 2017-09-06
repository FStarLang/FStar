module FStar.Monotonic.Heap

module S  = FStar.Set
module TS = FStar.TSet

open FStar.Preorder

let set  = Set.set
let tset = TSet.set

val heap :Type u#1

val equal: heap -> heap -> Type0

val equal_extensional (h1:heap) (h2:heap)
  :Lemma (requires True) (ensures (equal h1 h2 <==> h1 == h2))
         [SMTPat (equal h1 h2)]

val emp :heap

val mref (a:Type0) (rel:preorder a) :Type0

val addr_of: #a:Type0 -> #rel:preorder a -> mref a rel -> GTot nat

val is_mm: #a:Type0 -> #rel:preorder a -> mref a rel -> GTot bool

val compare_addrs:
  #a:Type0 -> #b:Type0 -> #rel1:preorder a -> #rel2:preorder b ->
  r1:mref a rel1 -> r2:mref b rel2 -> Tot (b:bool{b = (addr_of r1 = addr_of r2)})

val contains: #a:Type0 -> #rel:preorder a -> heap -> mref a rel -> Type0

val addr_unused_in: nat -> heap -> Type0

val unused_in: #a:Type0 -> #rel:preorder a -> mref a rel -> heap -> Type0

let fresh (#a:Type) (#rel:preorder a) (r:mref a rel) (h0:heap) (h1:heap) =
  r `unused_in` h0 /\ h1 `contains` r

let only_t (#a:Type0) (#rel:preorder a) (x:mref a rel) :GTot (tset nat) = TS.singleton (addr_of x)

let only (#a:Type0) (#rel:preorder a) (x:mref a rel) :GTot (set nat) = S.singleton (addr_of x)

let op_Hat_Plus_Plus (#a:Type0) (#rel:preorder a) (r:mref a rel) (s:set nat) :GTot (set nat) = S.union (only r) s

let op_Plus_Plus_Hat (#a:Type0) (#rel:preorder a) (s:set nat) (r:mref a rel) :GTot (set nat) = S.union s (only r)

let op_Hat_Plus_Hat (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (r1:mref a rel1) (r2:mref b rel2)
  :GTot (set nat) = S.union (only r1) (only r2)

val sel_tot: #a:Type0 -> #rel:preorder a -> h:heap -> r:mref a rel{h `contains` r} -> Tot a

val sel: #a:Type0 -> #rel:preorder a -> heap -> mref a rel -> GTot a

let valid_upd (#a:Type0) (#rel:preorder a) (h:heap) (r:mref a rel) (x:a) = rel (sel h r) x

val upd_tot: #a:Type0 -> #rel:preorder a -> h:heap -> r:mref a rel{h `contains` r} -> x:a{valid_upd h r x} -> Tot heap

val upd: #a:Type0 -> #rel:preorder a -> h:heap -> r:mref a rel -> x:a -> GTot heap

val alloc: #a:Type0 -> rel:preorder a -> heap -> a -> mm:bool -> Tot (mref a rel * heap)

val free_mm: #a:Type0 -> #rel:preorder a -> h:heap -> r:mref a rel{h `contains` r /\ is_mm r} -> GTot heap

let modifies_t (s:tset nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)}
                               ((~ (TS.mem (addr_of r) s)) /\ h0 `contains` r) ==> sel h1 r == sel h0 r) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (contains h1 r)}
                               h0 `contains` r ==> h1 `contains` r) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (r `unused_in` h0)}
                               r `unused_in` h1 ==> r `unused_in` h0)

let modifies (s:set nat) (h0:heap) (h1:heap) = modifies_t (TS.tset_of_set s) h0 h1

let equal_dom (h1:heap) (h2:heap) :GTot Type0 =
  (forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r <==> h2 `contains` r) /\
  (forall (a:Type0) (rel:preorder a) (r:mref a rel). r `unused_in` h1 <==> r `unused_in` h2)

val lemma_ref_unused_iff_addr_unused (#a:Type0) (#rel:preorder a) (h:heap) (r:mref a rel)
  :Lemma (requires True)
         (ensures  (r `unused_in` h <==> addr_of r `addr_unused_in` h))
	 [SMTPatOr [[SMTPat (r `unused_in` h)]; [SMTPat (addr_of r `addr_unused_in` h)]]]

val lemma_contains_implies_used (#a:Type0) (#rel:preorder a) (h:heap) (r:mref a rel)
  :Lemma (requires (h `contains` r))
         (ensures  (~ (r `unused_in` h)))
	 [SMTPatOr [[SMTPat (h `contains` r)]; [SMTPat (r `unused_in` h)]]]

val lemma_distinct_addrs_distinct_types
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:heap) (r1:mref a rel1) (r2:mref b rel2)
  :Lemma (requires (a =!= b /\ h `contains` r1 /\ h `contains` r2))
         (ensures  (addr_of r1 <> addr_of r2))
	 [SMTPatT (h `contains` r1); SMTPatT (h `contains` r2)]

val lemma_distinct_addrs_distinct_preorders
  (#a:Type0) (#rel1:preorder a) (#rel2:preorder a) (h:heap) (r1:mref a rel1) (r2:mref a rel2)
  :Lemma (requires (rel1 =!= rel2 /\ h `contains` r1 /\ h `contains` r2))
         (ensures  (addr_of r1 <> addr_of r2))
	 [SMTPatT (h `contains` r1); SMTPatT (h `contains` r2)]

(*
 * AR: this is a bit surprising. i had to add ~ (r1 === r2) postcondition to make the lemma
 * lemma_live_1 in hyperstack to go through. if addr_of r1 <> addr_of r2, shouldn't we get ~ (r1 === r2)
 * automatically? should dig into smt encoding to figure.
 *)
val lemma_distinct_addrs_unused
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:heap) (r1:mref a rel1) (r2:mref b rel2)
  :Lemma (requires (r1 `unused_in` h /\ ~ (r2 `unused_in` h)))
         (ensures  (addr_of r1 <> addr_of r2 /\ (~ (r1 === r2))))
         [SMTPat (r1 `unused_in` h); SMTPat (r2 `unused_in` h)]

val lemma_alloc (#a:Type0) (rel:preorder a) (h0:heap) (x:a) (mm:bool)
  :Lemma (requires True)
         (ensures  (let r, h1 = alloc rel h0 x mm in
                    fresh r h0 h1 /\ valid_upd h0 r x /\ h1 == upd h0 r x /\ is_mm r = mm))
	 [SMTPat (alloc rel h0 x mm)]

val lemma_free_mm_sel
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h0:heap)
  (r1:mref a rel1{h0 `contains` r1 /\ is_mm r1}) (r2:mref b rel2)
  :Lemma (requires True)
         (ensures  (addr_of r2 <> addr_of r1 ==> sel h0 r2 == sel (free_mm h0 r1) r2))
	 [SMTPat (sel (free_mm h0 r1) r2)]

val lemma_free_mm_contains
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h0:heap)
  (r1:mref a rel1{h0 `contains` r1 /\ is_mm r1}) (r2:mref b rel2)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r1 in
	            (addr_of r2 <> addr_of r1 /\ h0 `contains` r2) <==> h1 `contains` r2))
	 [SMTPat ((free_mm h0 r1) `contains` r2)]

val lemma_free_mm_unused
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h0:heap)
  (r1:mref a rel1{h0 `contains` r1 /\ is_mm r1}) (r2:mref b rel2)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r1 in
	            ((addr_of r1 = addr_of r2 ==> r2 `unused_in` h1)      /\
		     (r2 `unused_in` h0       ==> r2 `unused_in` h1)      /\
		     (r2 `unused_in` h1       ==> (r2 `unused_in` h0 \/ addr_of r2 = addr_of r1)))))
	 [SMTPat (r2 `unused_in` (free_mm h0 r1))]

(*
 * AR: we can prove this lemma only if both the mreferences have same preorder
 *)
val lemma_sel_same_addr (#a:Type0) (#rel:preorder a) (h:heap) (r1:mref a rel) (r2:mref a rel)
  :Lemma (requires (h `contains` r1 /\ addr_of r1 = addr_of r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
	 [SMTPat (sel h r1); SMTPat (sel h r2)]

val lemma_upd_same_addr (#a: Type0) (#rel: preorder a) (h: heap) (r1 r2: mref a rel) (x: a)
  :Lemma (requires ((h `contains` r1 \/ h `contains` r2) /\ addr_of r1 = addr_of r2))
         (ensures (upd h r1 x == upd h r2 x))
         [SMTPat (upd h r1 x); SMTPat (upd h r2 x)]

 (*
  * AR: this is true only if the preorder is same, else r2 may not be contained in h
  *)
val lemma_sel_upd1 (#a:Type0) (#rel:preorder a) (h:heap) (r1:mref a rel) (x:a{valid_upd h r1 x}) (r2:mref a rel)
  :Lemma (requires (addr_of r1 = addr_of r2))
         (ensures  (sel (upd h r1 x) r2 == x))
         [SMTPat (sel (upd h r1 x) r2)]

val lemma_sel_upd2 (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:heap) (r1:mref a rel1) (r2:mref b rel2) (x:b{valid_upd h r2 x})
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  (sel (upd h r2 x) r1 == sel h r1))
	 [SMTPat (sel (upd h r2 x) r1)]

val lemma_mref_injectivity
  :(u:unit{forall (a:Type0) (b:Type0) (rel1:preorder a) (rel2:preorder b) (r1:mref a rel1) (r2:mref b rel2). a =!= b ==> ~ (eq3 r1 r2)})

val lemma_in_dom_emp (#a:Type0) (#rel:preorder a) (r:mref a rel)
  :Lemma (requires True)
         (ensures  (r `unused_in` emp))
	 [SMTPat (r `unused_in` emp)]

val lemma_upd_contains (#a:Type0) (#rel:preorder a) (h:heap) (r:mref a rel) (x:a{valid_upd h r x})
  :Lemma (requires True)
         (ensures  ((upd h r x) `contains` r))
	 [SMTPat ((upd h r x) `contains` r)]

val lemma_well_typed_upd_contains
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:heap) (r1:mref a rel1) (x:a{valid_upd h r1 x}) (r2:mref b rel2)
  :Lemma (requires (h `contains` r1))
         (ensures  (let h1 = upd h r1 x in
	            h1 `contains` r2 <==> h `contains` r2))
	 [SMTPat ((upd h r1 x) `contains` r2)]

val lemma_unused_upd_contains
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:heap) (r1:mref a rel1) (x:a{valid_upd h r1 x}) (r2:mref b rel2)
  :Lemma (requires (r1 `unused_in` h))
         (ensures  (let h1 = upd h r1 x in
	            (h `contains` r2  ==> h1 `contains` r2) /\
		    (h1 `contains` r2 ==> (h `contains` r2 \/ addr_of r2 = addr_of r1))))
	 [SMTPat ((upd h r1 x) `contains` r2)]

val lemma_upd_contains_different_addr
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:heap) (r1:mref a rel1) (x:a{valid_upd h r1 x}) (r2:mref b rel2)
  :Lemma (requires (h `contains` r2 /\ addr_of r1 <> addr_of r2))
         (ensures  ((upd h r1 x) `contains` r2))
	 [SMTPat ((upd h r1 x) `contains` r2)]

val lemma_upd_unused
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:heap) (r1:mref a rel1) (x:a{valid_upd h r1 x}) (r2:mref b rel2)
  :Lemma (requires True)
         (ensures  ((addr_of r1 <> addr_of r2 /\ r2 `unused_in` h) <==> r2 `unused_in` (upd h r1 x)))
	 [SMTPat (r2 `unused_in` (upd h r1 x))]

val lemma_contains_upd_modifies (#a:Type0) (#rel:preorder a) (h:heap) (r:mref a rel) (x:a{valid_upd h r x})
  :Lemma (requires (h `contains` r))
         (ensures  (modifies (S.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x)]

val lemma_unused_upd_modifies (#a:Type0) (#rel:preorder a) (h:heap) (r:mref a rel) (x:a{valid_upd h r x})
  :Lemma (requires (r `unused_in` h))
         (ensures  (modifies (Set.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x); SMTPatT (r `unused_in` h)]

val upd_upd_same_mref
  (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel)
  (x:a{valid_upd h r x}) (y:a{valid_upd (upd h r x) r y})
  :Lemma (requires True)
         (ensures  (valid_upd h r y /\ (upd (upd h r x) r y == upd h r y)))
	 [SMTPat (upd (upd h r x) r y)]

val lemma_sel_equals_sel_tot_for_contained_refs
  (#a:Type0) (#rel:preorder a) (h:heap) (r:mref a rel{h `contains` r})
  :Lemma (requires True)
         (ensures  (sel_tot h r == sel h r))
	 [SMTPat (sel_tot h r)]

val lemma_upd_equals_upd_tot_for_contained_refs
  (#a:Type0) (#rel:preorder a) (h:heap) (r:mref a rel{h `contains` r}) (x:a{valid_upd h r x})
  :Lemma (requires True)
         (ensures  (upd_tot h r x == upd h r x))
	 [SMTPat (upd_tot h r x)]

val lemma_modifies_and_equal_dom_sel_diff_addr
  (#a:Type0)(#rel:preorder a) (s:set nat) (h0:heap) (h1:heap) (r:mref a rel)
  :Lemma (requires (modifies s h0 h1 /\ equal_dom h0 h1 /\ (~ (S.mem (addr_of r) s))))
         (ensures  (sel h0 r == sel h1 r))
	 [SMTPat (modifies s h0 h1); SMTPat (equal_dom h0 h1); SMTPat (sel h1 r)]

(*** Untyped views of monotonic references *)

(* Definition and ghost decidable equality *)
val aref: Type0
val dummy_aref: aref
val aref_equal (a1 a2: aref) : Ghost bool (requires True) (ensures (fun b -> b == true <==> a1 == a2))

(* Introduction rule *)
val aref_of: #t: Type0 -> #rel: preorder t -> r: mref t rel -> Tot aref

(* Operators lifted from ref *)
val addr_of_aref: a: aref -> GTot nat
val addr_of_aref_of: #t: Type0 -> #rel: preorder t -> r: mref t rel -> Lemma (addr_of r == addr_of_aref (aref_of r))
[SMTPat (addr_of_aref (aref_of r))]
val aref_is_mm: aref -> GTot bool
val is_mm_aref_of: #t: Type0 -> #rel: preorder t -> r: mref t rel -> Lemma (is_mm r == aref_is_mm (aref_of r))
[SMTPat (aref_is_mm (aref_of r))]
val aref_unused_in: aref -> heap -> Type0
val unused_in_aref_of: #t: Type0 -> #rel: preorder t -> r: mref t rel -> h: heap -> Lemma (unused_in r h <==> aref_unused_in (aref_of r) h)
[SMTPat (aref_unused_in (aref_of r) h)]
val contains_aref_unused_in: #a:Type -> #rel: preorder a -> h:heap -> x:mref a rel -> y:aref -> Lemma
  (requires (contains h x /\ aref_unused_in y h))
  (ensures  (addr_of x <> addr_of_aref y))

(* Elimination rule *)
val aref_live_at: h: heap -> a: aref -> t: Type0 -> rel: preorder t -> GTot Type0
val gref_of: a: aref -> t: Type0 -> rel: preorder t -> Ghost (mref t rel) (requires (exists h . aref_live_at h a t rel)) (ensures (fun _ -> True))
val ref_of: h: heap -> a: aref -> t: Type0 -> rel: preorder t -> Pure (mref t rel) (requires (aref_live_at h a t rel)) (ensures (fun x -> aref_live_at h a t rel /\ addr_of (gref_of a t rel) == addr_of x /\ is_mm x == aref_is_mm a))
val aref_live_at_aref_of
  (h: heap)
  (#t: Type0)
  (#rel: preorder t)
  (r: mref t rel)
: Lemma
  (ensures (aref_live_at h (aref_of r) t rel <==> contains h r))
  [SMTPat (aref_live_at h (aref_of r) t rel)]
val contains_gref_of
  (h: heap)
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h' . aref_live_at h' a t rel))
  (ensures ((exists h' . aref_live_at h' a t rel) /\ (contains h (gref_of a t rel) <==> aref_live_at h a t rel)))
  [SMTPatOr [
    [SMTPat (contains h (gref_of a t rel))];
    [SMTPat (aref_live_at h a t rel)];
  ]]

val aref_of_gref_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ aref_of (gref_of a t rel) == a))
  [SMTPat (aref_of (gref_of a t rel))]

(* Operators lowered to ref *)
abstract
let addr_of_gref_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ addr_of (gref_of a t rel) == addr_of_aref a))
  [SMTPat (addr_of (gref_of a t rel))]
= addr_of_aref_of (gref_of a t rel)

abstract
let is_mm_gref_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ is_mm (gref_of a t rel) == aref_is_mm a))
  [SMTPat (is_mm (gref_of a t rel))]
= is_mm_aref_of (gref_of a t rel)

abstract
let unused_in_gref_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
  (h: heap)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ (unused_in (gref_of a t rel) h <==> aref_unused_in a h)))
  [SMTPat (unused_in (gref_of a t rel) h)]
= unused_in_aref_of (gref_of a t rel) h

abstract
let sel_ref_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
  (h1 h2: heap)
: Lemma
  (requires (aref_live_at h1 a t rel /\ aref_live_at h2 a t rel))
  (ensures (aref_live_at h2 a t rel /\ sel h1 (ref_of h2 a t rel) == sel h1 (gref_of a t rel)))
  [SMTPat (sel h1 (ref_of h2 a t rel))]
= ()

abstract
let upd_ref_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
  (h1 h2: heap)
  (x: t)
: Lemma
  (requires (aref_live_at h1 a t rel /\ aref_live_at h2 a t rel))
  (ensures (aref_live_at h2 a t rel /\ upd h1 (ref_of h2 a t rel) x == upd h1 (gref_of a t rel) x))
  [SMTPat (upd h1 (ref_of h2 a t rel) x)]
= ()

(* Work around #1088 *)
val _eof: unit
