module FStar.Heap

open FStar.Classical
open FStar.Set

(* Heap is a tuple of a source of freshness (the no. of the next 
   reference to be allocated) and a mapping of allocated raw 
   references (represented as natural numbers) to types and values. *)

abstract noeq type heap_rec = {
  next_addr: nat;
  memory   : nat -> Tot (option (a:Type0 & a))
}  
abstract type heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

(* Consistency of heaps. aka, no strong updates *)
private let consistent (h0:heap) (h1:heap)
  = forall n x y. (h0.memory n == Some x /\ h1.memory n == Some y) ==> dfst x == dfst y

(* References: address * initial value * manually managed flag *)
abstract noeq type ref (a:Type0) = {
  addr: nat;
  init: a;
  mm:   bool;  //manually managed flag
}  

abstract let addr_of (#a:Type) (r:ref a) :GTot nat = r.addr

abstract let is_mm (#a:Type) (r:ref a) :GTot bool = r.mm

abstract let compare_addrs (#a:Type) (#b:Type) (r1:ref a) (r2:ref b)
  :(b:bool{b = (addr_of r1 = addr_of r2)})
  = r1.addr = r2.addr

abstract let contains (#a:Type0) (h:heap) (r:ref a)
  = Some? (h.memory r.addr) /\ dfst (Some?.v (h.memory r.addr)) == a

abstract let unused_in (#a:Type) (r:ref a) (h:heap) :Type0
  = None? (h.memory r.addr)

let fresh (#a:Type) (r:ref a) (h0:heap) (h1:heap) =
  r `unused_in` h0 /\ h1 `contains` r

let only x = singleton (addr_of x)

(* Select. *)
private abstract let sel_tot (#a:Type) (h:heap) (r:ref a{h `contains` r}) :a
  = let Some (| _, x |) = h.memory r.addr in
    x

abstract let sel (#a:Type) (h:heap) (r:ref a) :GTot a
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r) then
      sel_tot #a h r
    else r.init

(* Update. *)
abstract let upd_tot (#a:Type) (h:heap) (r:ref a{h `contains` r}) (x:a) :heap
  = { h with memory = (fun r' -> if r.addr = r'
			      then Some (| a, x |)
                              else h.memory r') }

abstract let upd (#a:Type) (h:heap) (r:ref a) (x:a) :GTot heap
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r)
    then upd_tot h r x
    else
      if r.addr >= h.next_addr
      then (* alloc at r.addr *)
        { next_addr = r.addr + 1;
          memory    = (fun (r':nat) -> if r' = r.addr
	   		           then Some (| a, x |)
                                   else h.memory r') }
      else (* strong update at r.addr *)
        { h with memory = (fun r' -> if r' = r.addr
				  then Some (| a, x |)
                                  else h.memory r') }

(* Allocate. *)
abstract let alloc (#a:Type) (h:heap) (x:a) (mm:bool) :GTot (ref a * heap)
  = let r = { addr = h.next_addr; init = x; mm = mm } in
    r, upd #a h r x

abstract let free_mm (#a:Type) (h:heap) (r:ref a{h `contains` r /\ is_mm r})
  :GTot heap
  = { h with memory = (fun r' -> if r' = r.addr then None else h.memory r') }

let modifies (s:set nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
                         ((~ (mem (addr_of r) s)) /\ h0 `contains` r) ==> sel h1 r == sel h0 r) /\
  (forall (a:Type) (r:ref a).{:pattern (contains h1 r)}
                        h0 `contains` r ==> h1 `contains` r) /\
  (forall (a:Type) (r:ref a).{:pattern (r `unused_in` h0)}
                        r `unused_in` h1 ==> r `unused_in` h0)

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
	   (forall (b:Type) (r':ref b). (r'.addr <> r.addr /\ h0 `contains` r') ==> h1 `contains` r') /\
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
  = ()

let lemma_distinct_addrs_distinct_types
  (#a:Type) (#b:Type) (h:heap) (r1:ref a) (r2:ref b)
  :Lemma (requires (a =!= b /\ h `contains` r1 /\ h `contains` r2))
         (ensures  (addr_of r1 <> addr_of r2))
	 [SMTPatT (h `contains` r1); SMTPatT (h `contains` r2)]
  = ()

let lemma_distinct_addrs_unused
  (#a:Type) (#b:Type) (h:heap) (r1:ref a) (r2:ref b)
  :Lemma (requires (r1 `unused_in` h /\ ~ (r2 `unused_in` h)))
         (ensures  (addr_of r1 <> addr_of r2))
         [SMTPat (r1 `unused_in` h); SMTPat (r2 `unused_in` h)]
  = ()

let lemma_alloc (#a:Type) (h0:heap) (x:a) (mm:bool)
  :Lemma (requires True)
         (ensures  (let r, h1 = alloc h0 x mm in
                    h1 == upd h0 r x /\ fresh r h0 h1 /\ is_mm r = mm))
	 [SMTPat (alloc h0 x mm)]
  = ()

let lemma_free_mm_sel (#a:Type) (#b:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r}) (r':ref b)
  :Lemma (requires True)
         (ensures  (addr_of r' <> addr_of r ==> sel h0 r' == sel (free_mm h0 r) r'))
	 [SMTPat (sel (free_mm h0 r) r')]
  = ()

let lemma_free_mm_contains (#a:Type) (#b:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r}) (r':ref b)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r in
	            (addr_of r' <> addr_of r /\ h0 `contains` r') <==> h1 `contains` r'))
	 [SMTPat ((free_mm h0 r) `contains` r')]
  = ()

let lemma_free_mm_unused (#a:Type) (#b:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r}) (r':ref b)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r in
	            ((addr_of r = addr_of r' ==> r' `unused_in` h1)      /\
		     (r' `unused_in` h0      ==> r' `unused_in` h1)      /\
		     (r' `unused_in` h1      ==> (r' `unused_in` h0 \/ addr_of r' = addr_of r)))))
	 [SMTPat (r' `unused_in` (free_mm h0 r))]
  = ()

let lemma_sel_same_addr (#a:Type) (h:heap) (r1:ref a) (r2:ref a)
  :Lemma (requires (h `contains` r1 /\ addr_of r1 = addr_of r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
	 [SMTPat (sel h r1); SMTPat (sel h r2)]
  = ()

let lemma_sel_upd1 (#a:Type) (h:heap) (r:ref a) (x:a) (r':ref a)
  :Lemma (requires (addr_of r = addr_of r'))
         (ensures  (sel (upd h r x) r' == x))
         [SMTPat (sel (upd h r x) r')]

  = ()

let lemma_sel_upd2 (#a:Type) (#b:Type) (h:heap) (r1:ref a) (r2:ref b) (x:b)
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  (sel (upd h r2 x) r1 == sel h r1))
	 [SMTPat (sel (upd h r2 x) r1)]
  = ()

let lemma_ref_injectivity
  :(u:unit{forall (a:Type) (b:Type) (r1:ref a) (r2:ref b). a =!= b ==> ~ (eq3 r1 r2)})
  = ()


let equal_dom (h1:heap) (h2:heap) :GTot Type0 =
  (forall (a:Type0) (r:ref a). h1 `contains` r <==> h2 `contains` r) /\
  (forall (a:Type0) (r:ref a). r `unused_in` h1 <==> r `unused_in` h2)

(* Empty. *)
let emp :heap = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

let lemma_in_dom_emp (#a:Type) (r:ref a)
  :Lemma (requires True)
         (ensures  (r `unused_in` emp))
	 [SMTPat (r `unused_in` emp)]
  = ()

let lemma_upd_contains (#a:Type) (h:heap) (r:ref a) (x:a)
  :Lemma (requires True)
         (ensures  ((upd h r x) `contains` r))
	 [SMTPat ((upd h r x) `contains` r)]
  = ()

let lemma_well_typed_upd_contains (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b)
  :Lemma (requires (h `contains` r))
         (ensures  (let h1 = upd h r x in
	            h1 `contains` r' <==> h `contains` r'))
	 [SMTPat ((upd h r x) `contains` r')]
  = ()

let lemma_unused_upd_contains (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b)
  :Lemma (requires (r `unused_in` h))
         (ensures  (let h1 = upd h r x in
	            (h `contains` r'  ==> h1 `contains` r') /\
		    (h1 `contains` r' ==> (h `contains` r' \/ addr_of r' = addr_of r))))
	 [SMTPat ((upd h r x) `contains` r')]
  = ()

let lemma_upd_contains_different_addr (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b)
  :Lemma (requires (h `contains` r' /\ addr_of r <> addr_of r'))
         (ensures  ((upd h r x) `contains` r'))
	 [SMTPat ((upd h r x) `contains` r')]
  = ()

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
  = ()

let lemma_contains_upd_modifies (#a:Type) (h:heap) (r:ref a) (x:a)
  :Lemma (requires (h `contains` r))
         (ensures  (modifies (Set.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x); SMTPat (h `contains` r)]
  = ()

let lemma_unused_upd_modifies (#a:Type) (h:heap) (r:ref a) (x:a)
  :Lemma (requires (r `unused_in` h))
         (ensures  (modifies (Set.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x); SMTPat (r `unused_in` h)]
  = ()

(* let lemma_modifies_trans (h1:heap) (h2:heap) (h3:heap) (s1:set nat) (s2:set nat) *)
(*   :Lemma (requires (modifies s1 h1 h2 /\ modifies s2 h2 h3)) *)
(*          (ensures  (modifies (union s1 s2) h1 h3)) *)
(* 	 [SMTPat (modifies s1 h1 h2); SMTPat (modifies s2 h2 h3)] *)
(*   = () *)

abstract let equal (h1:heap) (h2:heap) :Type0 =
  h1.next_addr = h2.next_addr /\
  FStar.FunctionalExtensionality.feq h1.memory h2.memory

val equal_extensional: h1:heap -> h2:heap
                       -> Lemma (requires True) (ensures (equal h1 h2 <==> h1 == h2))
		         [SMTPat (equal h1 h2)]
let equal_extensional h1 h2 = ()			 

let upd_upd_same_ref (#a:Type) (h:heap) (r:ref a) (x:a) (y:a)
  :Lemma (requires True)
         (ensures  (upd (upd h r x) r y == upd h r y))
	 [SMTPat (upd (upd h r x) r y)]
  = assert (equal (upd (upd h r x) r y) (upd h r y))

val op_Hat_Plus_Plus: #a:Type -> r:ref a -> set nat -> GTot (set nat)
let op_Hat_Plus_Plus #a r s = union (only r) s

val op_Plus_Plus_Hat: #a:Type -> set nat -> r:ref a -> GTot (set nat)
let op_Plus_Plus_Hat #a s r = union s (only r)

val op_Hat_Plus_Hat: #a:Type -> #b:Type -> ref a -> ref b -> GTot (set nat)
let op_Hat_Plus_Hat #a #b r1 r2 = union (only r1) (only r2)

abstract let upd_addr (#a:Type0) (h:heap) (addr:nat) (x:a) :heap =
  let next = if addr >= h.next_addr then addr + 1 else h.next_addr in
  let m = fun r -> if r = addr then Some (| a, x |) else h.memory r in
  { h with next_addr = next; memory = m }

let lemma_upd_addr_sel_same_addr (#a:Type0) (h0:heap) (addr:nat) (x:a) (r:ref a)
  :Lemma (requires (addr_of r = addr))
         (ensures  (let h1 = upd_addr h0 addr x in
	            sel h1 r == x))
	 [SMTPat (sel (upd_addr h0 addr x) r)]
  = ()

let lemma_upd_addr_sel_different_addr (#a:Type0) (#b:Type0) (h0:heap) (addr:nat) (x:a) (r:ref b)
  :Lemma (requires (addr_of r <> addr))
         (ensures  (let h1 = upd_addr h0 addr x in
		    sel h1 r == sel h0 r))
	 [SMTPat (sel (upd_addr h0 addr x) r)]
  = ()

let lemma_upd_addr_contains_same_addr (#a:Type0) (h0:heap) (addr:nat) (x:a) (r:ref a)
  :Lemma (requires (addr_of r = addr))
         (ensures  (let h1 = upd_addr h0 addr x in
                    h1 `contains` r))
	 [SMTPat ((upd_addr h0 addr x) `contains` r)]
  = ()

let lemma_upd_addr_contains_different_addr (#a:Type0) (#b:Type0) (h0:heap) (addr:nat) (x:a) (r:ref b)
  :Lemma (requires (addr_of r <> addr))
         (ensures  (let h1 = upd_addr h0 addr x in
	            h1 `contains` r <==> h0 `contains` r))
	 [SMTPat ((upd_addr h0 addr x) `contains` r)]
  = ()

let lemma_upd_addr_unused (#a:Type) (h0:heap) (addr:nat) (x:a) (r:ref a)
  :Lemma (requires True)
         (ensures  ((addr_of r <> addr /\ r `unused_in` h0) <==> r `unused_in` (upd_addr h0 addr x)))
	 [SMTPat (r `unused_in` (upd_addr h0 addr x))]
  = ()
