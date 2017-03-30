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

(* References: address * initial value *)
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

(* Select. *)
private abstract let sel_tot (#a:Type) (h:heap) (r:ref a{h `contains` r}) :a
  = let Some (| _, x |) = h.memory r.addr in
    x

abstract let sel (#a:Type) (h:heap) (r:ref a) :GTot a
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r) then
      sel_tot #a h r
    else r.init

(* Update. *)
private abstract let upd_tot (#a:Type) (h:heap) (r:ref a{h `contains` r}) (x:a) :heap
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
abstract let alloc (#a:Type) (h:heap) (x:a) :GTot (ref a * heap)
  = let r = { addr = h.next_addr; init = x; mm = false } in
    r, upd #a h r x

abstract let alloc_mm (#a:Type) (h:heap) (x:a)
  :Ghost (ref a * heap) (requires True) (ensures (fun (r, _) -> is_mm r))
  = let r = { addr = h.next_addr; init = x; mm = true } in
    r, upd #a h r x

private let contains_not_necessarily_well_typed (#a:Type) (h:heap) (r:ref a) :Type0 = Some? (h.memory r.addr)

abstract let does_not_contain (#a:Type) (h:heap) (r:ref a) :Type0 = ~ (contains_not_necessarily_well_typed h r)

(*
 * AR: the precondition here is stronger, we only require h `contains_not_necessarily_well_typed`
 * but i am trying a discipline where contains_not_necessarily_well_typed is not exported
 *)
abstract let free_mm (#a:Type) (h:heap) (r:ref a{h `contains` r /\ is_mm r})
  :GTot heap
  = { h with memory = (fun r' -> if r' = r.addr then None else h.memory r') }

(** some lemmas that summarize the behavior **)

(*
 * update of a well-typed reference
 *)
private let lemma_upd_contains
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma (h0 `contains` r ==>
          (let h1 = upd h0 r x in
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	   (forall (b:Type) (r':ref b). h0 `contains_not_necessarily_well_typed` r' ==> h1 `contains_not_necessarily_well_typed` r')))
  = ()

(*
 * update of a reference that is mapped but not necessarily well-typed
 * we cannot prove that h0 `contains_a_well_typed` r' ==> h1 `contains_a_well_typed` r'
 * because consider that in h0 (r:ref a) contains (| b, y:b |),
 * and that (r':ref b) s.t. r'.addr = r.addr
 * in h0, r' is well-typed, but in h1 it's not
 *)
private let lemma_upd_contains_not_necessarily_well_typed
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma (h0 `contains_not_necessarily_well_typed` r ==>
          (let h1 = upd h0 r x in
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')           /\
	   (forall (b:Type) (r':ref b). (r'.addr <> r.addr /\ h0 `contains` r') ==> h1 `contains` r') /\
	   (forall (b:Type) (r':ref b). h0 `contains_not_necessarily_well_typed` r' ==> h1 `contains_not_necessarily_well_typed` r')))
  = ()

(*
 * update of an unmapped reference
 *)
private let lemma_upd_unmapped
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma (~ (h0 `contains_not_necessarily_well_typed` r) ==>
          (let h1 = upd h0 r x in
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	   (forall (b:Type) (r':ref b). h0 `contains_not_necessarily_well_typed` r' ==> h1 `contains_not_necessarily_well_typed` r')))
  = ()

(*
 * alloc and alloc_mm behaves just like upd of an unmapped reference
 *)
private let lemma_alloc
  (#a:Type) (h0:heap) (x:a)
  :Lemma (let (r, h1) = alloc h0 x in
          ~ (h0 `contains_not_necessarily_well_typed` r) /\
	  h1 `contains` r                                /\
          not (is_mm r)                                                              /\
          (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
          (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	  (forall (b:Type) (r':ref b). h0 `contains_not_necessarily_well_typed` r' ==> h1 `contains_not_necessarily_well_typed` r'))
  = ()

private let lemma_alloc_mm
  (#a:Type) (h0:heap) (x:a)
  :Lemma (let (r, h1) = alloc_mm h0 x in
          ~ (h0 `contains_not_necessarily_well_typed` r) /\
	  h1 `contains` r                                /\
          is_mm r                                                                    /\
          (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	  (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	  (forall (b:Type) (r':ref b). h0 `contains_not_necessarily_well_typed` r' ==> h1 `contains_not_necessarily_well_typed` r'))
  = ()

private let lemma_free_mm (#a:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r})
  :Lemma (let h1 = free_mm h0 r in
          (~ (h1 `contains_not_necessarily_well_typed` r)) /\
	  (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==>
	                          ((sel h0 r' == sel h1 r'                 /\
				   (h0 `contains` r' ==> h1 `contains` r') /\
				   (h0 `contains_not_necessarily_well_typed` r' ==> h1 `contains_not_necessarily_well_typed` r')))))
  = ()

(** **)

let contains_implies_not_does_not_contain
  (#a:Type) (h:heap) (r:ref a)
  :Lemma (requires (h `contains` r))
         (ensures  (~ (h `does_not_contain` r)))
	 [SMTPatOr [[SMTPat (h `contains` r)]; [SMTPat (h `does_not_contain` r)]]]
  = ()

let does_not_contain_addr_of
  (#a:Type) (#b:Type) (h:heap) (r1:ref a) (r2:ref b)
  :Lemma (requires (h `does_not_contain` r1 /\ ~ (h `does_not_contain` r2)))
         (ensures  (addr_of r1 <> addr_of r2))
         [SMTPat (h `does_not_contain` r1); SMTPat (h `does_not_contain` r2)]
  = ()

(*
 * this is as from the previous heap, the pattern also
 *)
let fresh (s:set nat) (h0:heap) (h1:heap) =
  forall (a:Type) (r:ref a).{:pattern (h0 `contains_not_necessarily_well_typed` r)}
                       mem (addr_of r) s ==> (h0 `does_not_contain` r) /\ (h1 `contains` r)

let only x = singleton (addr_of x)

let alloc_lemma (#a:Type) (h0:heap) (x:a)
  :Lemma (requires True)
         (ensures  (let r, h1 = alloc h0 x in
                    h1 == upd h0 r x /\ h0 `does_not_contain` r /\ h1 `contains` r /\ not (is_mm r)))
	 [SMTPat (alloc h0 x)]
  = ()

let alloc_mm_lemma (#a:Type) (h0:heap) (x:a)
  :Lemma (requires True)
         (ensures  (let r, h1 = alloc_mm h0 x in
                    h1 == upd h0 r x /\ h0 `does_not_contain` r /\ h1 `contains` r /\ is_mm r))
	 [SMTPat (alloc_mm h0 x)]
  = ()

let free_mm_lemma_sel (#a:Type) (#b:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r}) (r':ref b)
  :Lemma (requires True)
         (ensures  (addr_of r' <> addr_of r ==> sel h0 r' == sel (free_mm h0 r) r'))
	 [SMTPat (sel (free_mm h0 r) r')]
  = ()

let free_mm_does_not_contain_same (#a:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r})
  :Lemma (requires True)
         (ensures  ((free_mm h0 r) `does_not_contain` r))
	 [SMTPat ((free_mm h0 r) `does_not_contain` r)]
  = ()

let free_mm_contains_diff (#a:Type) (#b:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r}) (r':ref b)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r in
	            (addr_of r' <> addr_of r /\ h0 `contains` r') ==> h1 `contains` r'))
	 [SMTPat ((free_mm h0 r) `contains` r')]
  = ()

let sel_same_addr (#a:Type) (h:heap) (r1:ref a) (r2:ref a)
  :Lemma (requires (h `contains` r1 /\ addr_of r1 = addr_of r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
	 [SMTPat (sel h r1); SMTPat (sel h r2)]
  = ()

let sel_upd1 (#a:Type) (h:heap) (r:ref a) (x:a) (r':ref a)
  :Lemma (requires (addr_of r = addr_of r'))
         (ensures  (sel (upd h r x) r' == x))
         [SMTPat (sel (upd h r x) r')]

  = ()

let sel_upd2 (#a:Type) (#b:Type) (h:heap) (r1:ref a) (r2:ref b) (x:b)
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  (sel (upd h r2 x) r1 == sel h r1))
	 [SMTPat (sel (upd h r2 x) r1)]
  = ()

(*
 * AR: I am pretty sure we can derive it, TODO
 *)
(* val upd_sel : #a:Type -> h:heap -> r:ref a ->  *)
(* 	      Lemma (requires (h `contains_a_well_typed` r)) *)
(* 	            (ensures  (upd h r (sel h r) == h)) *)
(* 	      [SMTPat (upd h r (sel h r))] *)
(* let upd_sel #a h r =  *)
(*   assert (FStar.FunctionalExtensionality.feq (upd h r (sel h r)).memory h.memory) *)

let equal_dom (h1:heap) (h2:heap) :GTot Type0 =
  forall (a:Type0) (r:ref a). h1 `contains_not_necessarily_well_typed` r <==> h2 `contains_not_necessarily_well_typed` r

(* Empty. *)
let emp :heap = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

let in_dom_emp (#a:Type) (r:ref a)
  :Lemma (requires True)
         (ensures  (emp `does_not_contain` r))
	 [SMTPat (emp `does_not_contain` r)]
  = ()

(*
 * see the 3 private lemmas for the behavior of update above
 *)
(* let upd_contains (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b) *)
(*   :Lemma (requires True) *)
(*          (ensures  (((upd h r x) `contains` r) /\ *)
(* 	            (h `contains_not_necessarily_well_typed` r' ==> (upd h r x) `contains_not_necessarily_well_typed` r'))) *)
(* 	 [SMTPat ((upd h r x) `contains_not_necessarily_well_typed` r')] *)
(*   = () *)

let upd_contains_a_well_typed (#a:Type) (#b:Type) (h:heap) (r:ref a) (x:a) (r':ref b)
  :Lemma (requires True)
         (ensures  (((upd h r x) `contains` r) /\

	            ((h `contains` r' /\  //if h contains_a_well_typed r' and

                      ((h `contains` r) \/  //either h contains_a_well_typed r
		       (h `does_not_contain` r)          \/  //or h does not contain r
		       (addr_of r <> addr_of r')))             //or r'.addr <> r.addr
		     ==> (upd h r x) `contains` r')))  //then updated heap contains_a_well_typed r'
         [SMTPat ((upd h r x) `contains` r')]
  = ()

let modifies (s:set nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
                         ((~ (mem (addr_of r) s)) /\ h0 `contains` r) ==> sel h1 r == sel h0 r) /\
  (forall (a:Type) (r:ref a).{:pattern (contains h1 r)}
                        h0 `contains` r ==> h1 `contains` r)
  (* (forall (a:Type) (r:ref a).{:pattern (h1 `contains_not_necessarily_well_typed` r)} *)
  (*                       h0 `contains_not_necessarily_well_typed` r ==> h1 `contains_not_necessarily_well_typed` r) /\ *)
  (* (forall (a:Type) (r:ref a).{:pattern (h1 `contains` r)} *)
  (*                       (~ (mem (addr_of r) s) /\ h0 `contains` r) ==> h1 `contains` r) *)

private let upd_modifies (#a:Type) (h:heap) (r:ref a{h `contains` r \/ h `does_not_contain` r}) (x:a)
  :Lemma (modifies (Set.singleton (addr_of r)) h (upd h r x))
  = ()

abstract val lemma_modifies_trans: m1:heap -> m2:heap -> m3:heap
                       -> s1:set nat -> s2:set nat
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                               (ensures (modifies (union s1 s2) m1 m3))
let lemma_modifies_trans m1 m2 m3 s1 s2 = ()

(*
 * AR: we don't have a public definition of heap equality, which is non-ideal
 * as it requires lemmas like upd_upd_same_ref below
 *)
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
