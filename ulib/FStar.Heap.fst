module FStar.Heap

open FStar.Classical
open FStar.Set

open FStar.Monotonic.Heap

(* Heap is a tuple of a source of freshness (the no. of the next 
   reference to be allocated) and a mapping of allocated raw 
   references (represented as natural numbers) to types and values. *)

abstract let heap = heap

abstract let ref (a:Type0) = mref a (fun _ _ -> True)

//private let as_mref (#a:Type0) (r:ref a) :Tot (mref a (fun _ _ -> True)) = r

abstract let addr_of (#a:Type) (r:ref a) :GTot nat = addr_of r

abstract let is_mm (#a:Type) (r:ref a) :GTot bool = is_mm r

abstract let compare_addrs (#a:Type) (#b:Type) (r1:ref a) (r2:ref b)
  :(b:bool{b = (addr_of r1 = addr_of r2)})
  = compare_addrs r1 r2

abstract val contains: #a:Type0 -> heap -> ref a -> GTot Type0
let contains #a h r = contains h r 

abstract val unused_in: #a:Type0 -> ref a -> heap -> GTot Type0
let unused_in #a r h = unused_in r h

abstract val fresh: #a:Type0 -> ref a -> heap -> heap -> GTot Type0
let fresh #a r h0 h1 = fresh r h0 h1

let only x = singleton (addr_of x)

(* Select. *)
private abstract let sel_tot (#a:Type) (h:heap) (r:ref a{h `contains` r}) :a
  = sel_tot h r

abstract let sel (#a:Type) (h:heap) (r:ref a) :GTot a
  = sel h r


(* Update. *)
abstract let upd_tot (#a:Type) (h:heap) (r:ref a{h `contains` r}) (x:a) :heap
  = upd_tot h r x

abstract let upd (#a:Type) (h:heap) (r:ref a) (x:a) :GTot heap
  = upd h r x

(* Allocate. *)
abstract let alloc (#a:Type) (h:heap) (x:a) (mm:bool) :GTot (ref a * heap)
  = alloc h x (fun _ _ -> True) mm
  
abstract let free_mm (#a:Type) (h:heap) (r:ref a{h `contains` r /\ is_mm r})
  :GTot heap
  = free_mm h r

val modifies: s:set nat -> heap -> heap -> GTot Type0
let modifies s h0 h1 = modifies s h0 h1

(** some lemmas that summarize the behavior **)


(*
 * update of a well-typed reference
 *)
private let lemma_upd_contains_test
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma (h0 `contains` r ==>
          (let h1 = upd h0 r x in
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (r':ref b). h0 `contains` r' <==> h1 `contains` r')             /\
	   (forall (b:Type) (r':ref b). r' `unused_in` h0  <==> r' `unused_in` h1)))
  = ()

(*
 * update of a reference that is mapped but not necessarily well-typed
 * we cannot prove that h0 `contains` r' ==> h1 `contains` r'
 * because consider that in h0 (r:ref a) contains (| b, y:b |),
 * and that (r':ref b) s.t. r'.addr = r.addr
 * in h0, r' is well-typed, but in h1 it's not
 *)
private let lemma_upd_contains_not_necessarily_well_typed_test
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma ((~ (r `unused_in` h0)) ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')           /\
	   (forall (b:Type) (r':ref b). (addr_of r' <> addr_of r /\ h0 `contains` r') ==> h1 `contains` r') /\
	   (forall (b:Type) (r':ref b). r' `unused_in` h0 <==> r' `unused_in` h1)))
  = ()

(*
 * update of an unused reference
 *)
private let lemma_upd_unused_test
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma (r `unused_in` h0 ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	   (forall (b:Type) (r':ref b). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1))))
  = ()

(*
 * alloc and alloc_mm behaves just like upd of an unmapped reference
 *)
private let lemma_alloc_test (#a:Type) (h0:heap) (x:a) (mm:bool)
  :Lemma (let (r, h1) = alloc h0 x mm in
          r `unused_in` h0 /\
	  h1 `contains` r  /\
          is_mm r = mm     /\
          (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
          (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	  (forall (b:Type) (r':ref b). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1)))
  = ()

private let lemma_free_mm_test (#a:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r})
  :Lemma (let h1 = free_mm h0 r in
          r `unused_in` h1 /\
	  (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==>
	                          ((sel h0 r' == sel h1 r'                 /\
				   (h0 `contains` r' <==> h1 `contains` r') /\
				   (r' `unused_in` h0 <==> r' `unused_in` h1)))))
  = ()

private let lemma_alloc_fresh_test (#a:Type) (h0:heap) (x:a) (mm:bool)
  :Lemma (let r, h1 = alloc h0 x mm in
          fresh r h0 h1 /\ modifies empty h0 h1)
  = ()

(** **)

let lemma_contains_implies_used
  (#a:Type) (h:heap) (r:ref a)
  :Lemma (requires (h `contains` r))
         (ensures  (~ (r `unused_in` h)))
	 [SMTPatOr [[SMTPat (h `contains` r)]; [SMTPat (r `unused_in` h)]]]
  = lemma_contains_implies_used h r

let lemma_distinct_addrs_distinct_types
  (#a:Type) (#b:Type) (h:heap) (r1:ref a) (r2:ref b)
  :Lemma (requires (a =!= b /\ h `contains` r1 /\ h `contains` r2))
         (ensures  (addr_of r1 <> addr_of r2))
	 [SMTPatT (h `contains` r1); SMTPatT (h `contains` r2)]
  = lemma_distinct_addrs_distinct_types h r1 r2

let lemma_distinct_addrs_unused
  (#a:Type) (#b:Type) (h:heap) (r1:ref a) (r2:ref b)
  :Lemma (requires (r1 `unused_in` h /\ ~ (r2 `unused_in` h)))
         (ensures  (addr_of r1 <> addr_of r2))
         [SMTPat (r1 `unused_in` h); SMTPat (r2 `unused_in` h)]
  = lemma_distinct_addrs_unused h r1 r2

let lemma_alloc (#a:Type) (h0:heap) (x:a) (mm:bool)
  :Lemma (requires True)
         (ensures  (let r, h1 = alloc h0 x mm in
                    h1 == upd h0 r x /\ fresh r h0 h1 /\ is_mm r = mm))
	 [SMTPat (alloc h0 x mm)]
  = lemma_alloc #a #(fun _ _ -> True) h0 x mm

let lemma_free_mm_sel (#a:Type) (#b:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r}) (r':ref b)
  :Lemma (requires True)
         (ensures  (addr_of r' <> addr_of r ==> sel h0 r' == sel (free_mm h0 r) r'))
	 [SMTPat (sel (free_mm h0 r) r')]
  = lemma_free_mm_sel h0 r r'

let lemma_free_mm_contains (#a:Type) (#b:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r}) (r':ref b)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r in
	            (addr_of r' <> addr_of r /\ h0 `contains` r') <==> h1 `contains` r'))
	 [SMTPat ((free_mm h0 r) `contains` r')]
  = lemma_free_mm_contains h0 r r'

let lemma_free_mm_unused (#a:Type) (#b:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r}) (r':ref b)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r in
	            ((addr_of r = addr_of r' ==> r' `unused_in` h1)      /\
		     (r' `unused_in` h0      ==> r' `unused_in` h1)      /\
		     (r' `unused_in` h1      ==> (r' `unused_in` h0 \/ addr_of r' = addr_of r)))))
	 [SMTPat (r' `unused_in` (free_mm h0 r))]
  = lemma_free_mm_unused_m h0 r r'

let lemma_sel_same_addr (#a:Type) (h:heap) (r1:ref a) (r2:ref a)
  :Lemma (requires (h `contains` r1 /\ addr_of r1 = addr_of r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
	 [SMTPat (sel h r1); SMTPat (sel h r2)]
  = lemma_sel_same_addr h r1 r2

let lemma_sel_upd1 (#a:Type) (h:heap) (r:ref a) (x:a) (r':ref a)
  :Lemma (requires (addr_of r = addr_of r'))
         (ensures  (sel (upd h r x) r' == x))
         [SMTPat (sel (upd h r x) r')]

  = lemma_sel_upd1 h r x r'

let lemma_sel_upd2 (#a:Type) (#b:Type) (h:heap) (r1:ref a) (r2:ref b) (x:b)
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  (sel (upd h r2 x) r1 == sel h r1))
	 [SMTPat (sel (upd h r2 x) r1)]
  = lemma_sel_upd2 h r1 r2 x

let lemma_ref_injectivity
  :(u:unit{forall (a:Type) (b:Type) (r1:ref a) (r2:ref b). a =!= b ==> ~ (eq3 r1 r2)})
  = lemma_ref_injectivity

let equal_dom (h1:heap) (h2:heap) :GTot Type0 = equal_dom h1 h2
//  forall (a:Type0) (r:ref a). r `unused_in` h1 <==> r `unused_in` h2

(* Empty. *)
let emp :heap = emp

(*let emp :heap = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}*)

let lemma_in_dom_emp (#a:Type) (r:ref a)
  :Lemma (requires True)
         (ensures  (r `unused_in` emp))
	 [SMTPat (r `unused_in` emp)]
  = lemma_in_dom_emp r

let lemma_upd_contains (#a:Type) (h:heap) (r:ref a) (x:a)
  :Lemma (requires True)
         (ensures  ((upd h r x) `contains` r))
	 [SMTPat ((upd h r x) `contains` r)]
  = lemma_upd_contains h r x

let lemma_well_typed_upd_contains (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b)
  :Lemma (requires (h `contains` r))
         (ensures  (let h1 = upd h r x in
	            h1 `contains` r' <==> h `contains` r'))
	 [SMTPat ((upd h r x) `contains` r')]
  = lemma_well_typed_upd_contains h r x r'

let lemma_unused_upd_contains (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b)
  :Lemma (requires (r `unused_in` h))
         (ensures  (let h1 = upd h r x in
	            (h `contains` r'  ==> h1 `contains` r') /\
		    (h1 `contains` r' ==> (h `contains` r' \/ addr_of r' = addr_of r))))
	 [SMTPat ((upd h r x) `contains` r')]
  = lemma_unused_upd_contains h r x r'

let lemma_upd_contains_different_addr (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b)
  :Lemma (requires (h `contains` r' /\ addr_of r <> addr_of r'))
         (ensures  ((upd h r x) `contains` r'))
	 [SMTPat ((upd h r x) `contains` r')]
  = lemma_upd_contains_different_addr h r x r'


(* let upd_contains (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b) *)
(*   :Lemma (requires True) *)
(*          (ensures  (((upd h r x) `contains` r) /\ *)

(* 	            ((h `contains` r' /\  //if h contains_a_well_typed r' and *)

(*                       ((h `contains` r) \/  //either h contains_a_well_typed r *)
(* 		       (r `unused_in` h) \/  //or h does not contain r *)
(* 		       (addr_of r <> addr_of r')))  //or r'.addr <> r.addr *)
(* 		     ==> (upd h r x) `contains` r')))  //then updated heap contains_a_well_typed r' *)
(*          [SMTPat ((upd h r x) `contains` r')] *)
(*   = () *)

let lemma_upd_unused (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b)
  :Lemma (requires True)
         (ensures  ((addr_of r <> addr_of r' /\ r' `unused_in` h) <==> r' `unused_in` (upd h r x)))
	 [SMTPat (r' `unused_in` (upd h r x))]
  = lemma_upd_unused h r x r'

let lemma_contains_upd_modifies (#a:Type) (h:heap) (r:ref a) (x:a)
  :Lemma (requires (h `contains` r))
         (ensures  (modifies (Set.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x); SMTPat (h `contains` r)]
  = lemma_contains_upd_modifies h r x

let lemma_unused_upd_modifies (#a:Type) (h:heap) (r:ref a) (x:a)
  :Lemma (requires (r `unused_in` h))
         (ensures  (modifies (Set.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x); SMTPat (r `unused_in` h)]
  = lemma_unused_upd_modifies h r x

(* let lemma_modifies_trans (h1:heap) (h2:heap) (h3:heap) (s1:set nat) (s2:set nat) *)
(*   :Lemma (requires (modifies s1 h1 h2 /\ modifies s2 h2 h3)) *)
(*          (ensures  (modifies (union s1 s2) h1 h3)) *)
(* 	 [SMTPat (modifies s1 h1 h2); SMTPat (modifies s2 h2 h3)] *)
(*   = () *)

abstract let equal (h1:heap) (h2:heap) :Type0 = equal h1 h2

val equal_extensional: h1:heap -> h2:heap
                       -> Lemma (requires True) (ensures (equal h1 h2 <==> h1 == h2))
		         [SMTPat (equal h1 h2)]
let equal_extensional h1 h2 = equal_extensional h1 h2			 

let upd_upd_same_ref (#a:Type) (h:heap) (r:ref a) (x:a) (y:a)
  :Lemma (requires True)
         (ensures  (upd (upd h r x) r y == upd h r y))
	 [SMTPat (upd (upd h r x) r y)]
  = () //assert (equal (upd (upd h r x) r y) (upd h r y))

val op_Hat_Plus_Plus: #a:Type -> r:ref a -> set nat -> GTot (set nat)
let op_Hat_Plus_Plus #a r s = union (only r) s

val op_Plus_Plus_Hat: #a:Type -> set nat -> r:ref a -> GTot (set nat)
let op_Plus_Plus_Hat #a s r = union s (only r)

val op_Hat_Plus_Hat: #a:Type -> #b:Type -> ref a -> ref b -> GTot (set nat)
let op_Hat_Plus_Hat #a #b r1 r2 = union (only r1) (only r2)


(* lemmas to pass regressions *)

(*let lemma_fresh_not_contained (#a:Type) (r:ref a) (h0:heap) (h1:heap) 
  :Lemma (requires (fresh r h0 h1))
         (ensures  (~(contains h0 r)))
	 [SMTPat (fresh r h0 h1)]
  = () //lemma_fresh_not_contained r h0 h1*)

