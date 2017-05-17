module FStar.Heap

module S  = FStar.Set
module TS = FStar.TSet

type set  = Set.set
type tset = TSet.set

val heap :Type u#1

val emp :heap

val ref (a:Type0) :Type0

val addr_of: #a:Type0 -> ref a -> GTot nat

val is_mm: #a:Type0 -> ref a -> GTot bool

val compare_addrs: #a:Type0 -> #b:Type0 -> r1:ref a -> r2:ref b -> Tot (b:bool{b = (addr_of r1 = addr_of r2)})

val contains: #a:Type0 -> heap -> ref a -> Type0

val unused_in: #a:Type0 -> ref a -> heap -> Type0

let fresh (#a:Type) (r:ref a) (h0:heap) (h1:heap) =
  r `unused_in` h0 /\ h1 `contains` r

let only_t x = TS.singleton (addr_of x)

let only x = S.singleton (addr_of x)

let op_Hat_Plus_Plus (#a:Type0) (r:ref a) (s:set nat) = S.union (only r) s

let op_Plus_Plus_Hat (#a:Type0) (s:set nat) (r:ref a) = S.union s (only r)

let op_Hat_Plus_Hat (#a:Type0) (#b:Type0) (r1:ref a) (r2:ref b) = S.union (only r1) (only r2)

val sel_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot a

val sel: #a:Type0 -> heap -> ref a -> GTot a

val upd_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> a -> Tot heap

val upd: #a:Type0 -> heap -> ref a -> a -> GTot heap

val alloc: #a:Type0 -> heap -> a -> mm:bool -> GTot (ref a * heap)

val free_mm: #a:Type0 -> h:heap -> r:ref a{h `contains` r /\ is_mm r} -> GTot heap

let modifies_t (s:tset nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
                         ((~ (TS.mem (addr_of r) s)) /\ h0 `contains` r) ==> sel h1 r == sel h0 r) /\
  (forall (a:Type) (r:ref a).{:pattern (contains h1 r)}
                        h0 `contains` r ==> h1 `contains` r) /\
  (forall (a:Type) (r:ref a).{:pattern (r `unused_in` h0)}
                        r `unused_in` h1 ==> r `unused_in` h0)

let modifies (s:set nat) (h0:heap) (h1:heap) = modifies_t (TS.tset_of_set s) h0 h1

let equal_dom (h1:heap) (h2:heap) :GTot Type0 =
  (forall (a:Type0) (r:ref a). h1 `contains` r <==> h2 `contains` r) /\
  (forall (a:Type0) (r:ref a). r `unused_in` h1 <==> r `unused_in` h2)

val lemma_contains_implies_used (#a:Type0) (h:heap) (r:ref a)
  :Lemma (requires (h `contains` r))
         (ensures  (~ (r `unused_in` h)))
	 [SMTPatOr [[SMTPat (h `contains` r)]; [SMTPat (r `unused_in` h)]]]

val lemma_distinct_addrs_distinct_types (#a:Type0) (#b:Type0) (h:heap) (r1:ref a) (r2:ref b)
  :Lemma (requires (a =!= b /\ h `contains` r1 /\ h `contains` r2))
         (ensures  (addr_of r1 <> addr_of r2))
	 [SMTPatT (h `contains` r1); SMTPatT (h `contains` r2)]

val lemma_distinct_addrs_unused (#a:Type0) (#b:Type0) (h:heap) (r1:ref a) (r2:ref b)
  :Lemma (requires (r1 `unused_in` h /\ ~ (r2 `unused_in` h)))
         (ensures  (addr_of r1 <> addr_of r2))
         [SMTPat (r1 `unused_in` h); SMTPat (r2 `unused_in` h)]

val lemma_alloc (#a:Type0) (h0:heap) (x:a) (mm:bool)
  :Lemma (requires True)
         (ensures  (let r, h1 = alloc h0 x mm in
                    h1 == upd h0 r x /\ fresh r h0 h1 /\ is_mm r = mm))
	 [SMTPat (alloc h0 x mm)]

val lemma_free_mm_sel (#a:Type0) (#b:Type0) (h0:heap) (r1:ref a{h0 `contains` r1 /\ is_mm r1}) (r2:ref b)
  :Lemma (requires True)
         (ensures  (addr_of r2 <> addr_of r1 ==> sel h0 r2 == sel (free_mm h0 r1) r2))
	 [SMTPat (sel (free_mm h0 r1) r2)]

val lemma_free_mm_contains (#a:Type0) (#b:Type0) (h0:heap) (r1:ref a{h0 `contains` r1 /\ is_mm r1}) (r2:ref b)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r1 in
	            (addr_of r2 <> addr_of r1 /\ h0 `contains` r2) <==> h1 `contains` r2))
	 [SMTPat ((free_mm h0 r1) `contains` r2)]

val lemma_free_mm_unused (#a:Type0) (#b:Type0) (h0:heap) (r1:ref a{h0 `contains` r1 /\ is_mm r1}) (r2:ref b)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r1 in
	            ((addr_of r1 = addr_of r2 ==> r2 `unused_in` h1)      /\
		     (r2 `unused_in` h0       ==> r2 `unused_in` h1)      /\
		     (r2 `unused_in` h1       ==> (r2 `unused_in` h0 \/ addr_of r2 = addr_of r1)))))
	 [SMTPat (r2 `unused_in` (free_mm h0 r1))]

val lemma_sel_same_addr (#a:Type0) (h:heap) (r1:ref a) (r2:ref a)
  :Lemma (requires (h `contains` r1 /\ addr_of r1 = addr_of r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
	 [SMTPat (sel h r1); SMTPat (sel h r2)]

val lemma_sel_upd1 (#a:Type0) (h:heap) (r1:ref a) (x:a) (r2:ref a)
  :Lemma (requires (addr_of r1 = addr_of r2))
         (ensures  (sel (upd h r1 x) r2 == x))
         [SMTPat (sel (upd h r1 x) r2)]

val lemma_sel_upd2 (#a:Type0) (#b:Type0) (h:heap) (r1:ref a) (r2:ref b) (x:b)
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  (sel (upd h r2 x) r1 == sel h r1))
	 [SMTPat (sel (upd h r2 x) r1)]

val lemma_ref_injectivity
  :(u:unit{forall (a:Type0) (b:Type0) (r1:ref a) (r2:ref b). a =!= b ==> ~ (eq3 r1 r2)})

val lemma_in_dom_emp (#a:Type0) (r:ref a)
  :Lemma (requires True)
         (ensures  (r `unused_in` emp))
	 [SMTPat (r `unused_in` emp)]

val lemma_upd_contains (#a:Type0) (h:heap) (r:ref a) (x:a)
  :Lemma (requires True)
         (ensures  ((upd h r x) `contains` r))
	 [SMTPat ((upd h r x) `contains` r)]

val lemma_well_typed_upd_contains (#a:Type0) (#b:Type0) (h:heap) (r1:ref a) (x:a) (r2:ref b)
  :Lemma (requires (h `contains` r1))
         (ensures  (let h1 = upd h r1 x in
	            h1 `contains` r2 <==> h `contains` r2))
	 [SMTPat ((upd h r1 x) `contains` r2)]

val lemma_unused_upd_contains (#a:Type0) (#b:Type0) (h:heap) (r1:ref a) (x:a) (r2:ref b)
  :Lemma (requires (r1 `unused_in` h))
         (ensures  (let h1 = upd h r1 x in
	            (h `contains` r2  ==> h1 `contains` r2) /\
		    (h1 `contains` r2 ==> (h `contains` r2 \/ addr_of r2 = addr_of r1))))
	 [SMTPat ((upd h r1 x) `contains` r2)]

val lemma_upd_contains_different_addr (#a:Type0) (#b:Type0) (h:heap) (r1:ref a) (x:a) (r2:ref b)
  :Lemma (requires (h `contains` r2 /\ addr_of r1 <> addr_of r2))
         (ensures  ((upd h r1 x) `contains` r2))
	 [SMTPat ((upd h r1 x) `contains` r2)]

val lemma_upd_unused (#a:Type0) (#b:Type0) (h:heap) (r1:ref a) (x:a) (r2:ref b)
  :Lemma (requires True)
         (ensures  ((addr_of r1 <> addr_of r2 /\ r2 `unused_in` h) <==> r2 `unused_in` (upd h r1 x)))
	 [SMTPat (r2 `unused_in` (upd h r1 x))]

val lemma_contains_upd_modifies (#a:Type0) (h:heap) (r:ref a) (x:a)
  :Lemma (requires (h `contains` r))
         (ensures  (modifies (S.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x); SMTPatT (h `contains` r)]

val lemma_unused_upd_modifies (#a:Type0) (h:heap) (r:ref a) (x:a)
  :Lemma (requires (r `unused_in` h))
         (ensures  (modifies (Set.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x); SMTPatT (r `unused_in` h)]

val equal: heap -> heap -> Type0

val equal_extensional (h1:heap) (h2:heap)
  :Lemma (requires True) (ensures (equal h1 h2 <==> h1 == h2))
         [SMTPat (equal h1 h2)]

val upd_upd_same_ref (#a:Type) (h:heap) (r:ref a) (x:a) (y:a)
  :Lemma (requires True)
         (ensures  (upd (upd h r x) r y == upd h r y))
	 [SMTPat (upd (upd h r x) r y)]
