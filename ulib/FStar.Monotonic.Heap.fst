module FStar.Monotonic.Heap

open FStar.Classical
open FStar.Set
open FStar.StrongExcludedMiddle

open FStar.Preorder

(* Preordered relations and stable predicates *)


(* Heap is a tuple of a source of freshness (the no. of the next 
   reference to be allocated) and a mapping of allocated raw 
   references (represented as natural numbers) to types and values. *)

abstract noeq type heap_rec = {
  next_addr: nat;
  memory   : nat -> Tot (option (a:Type0 & (a * preorder a)))
}  

abstract type heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

(* Consistency of heaps. aka, no strong updates *)
private let consistent (h0:heap) (h1:heap)
  = forall n x y. (h0.memory n == Some x /\ h1.memory n == Some y) ==> dfst x == dfst y

(* References: address * initial value * manually managed flag *)
abstract noeq type mref (a:Type0) (rel:preorder a) = {
  addr: nat;
  init: a;
  mm:   bool;  //manually managed flag
}  

abstract let addr_of (#a:Type) (#rel:preorder a) (r:mref a rel) :GTot nat = r.addr

abstract let is_mm (#a:Type) (#rel:preorder a) (r:mref a rel) :GTot bool = r.mm

abstract let compare_addrs (#a:Type) (#b:Type) (#rela:preorder a) (#relb:preorder b) (r1:mref a rela) (r2:mref b relb)
  :(b:bool{b = (addr_of r1 = addr_of r2)})
  = r1.addr = r2.addr

abstract let contains (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel)
//  = exists x . (h.memory r.addr == Some (| a , (x, rel) |))
  = Some? (h.memory r.addr) 
 /\ dfst (Some?.v (h.memory r.addr)) == a 
 /\ snd #(dfst (Some?.v (h.memory r.addr))) #(preorder a) (dsnd (Some?.v (h.memory r.addr))) == rel


abstract let unused_in (#a:Type) (#rel:preorder a) (r:mref a rel) (h:heap) :Type0
  = None? (h.memory r.addr)

let fresh (#a:Type) (#rel:preorder a) (r:mref a rel) (h0:heap) (h1:heap) 
  = r `unused_in` h0 /\ h1 `contains` r

val only: #a:Type -> #rel:preorder a -> mref a rel -> GTot (set nat)
let only #a #rel r = singleton (addr_of r)

(* Select. *)
abstract let sel_tot (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel{h `contains` r}) :Tot a
  = let Some (| _, (x, _) |) = h.memory r.addr in
    x

abstract let sel (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel) :GTot a
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r) then
      sel_tot #a h r
    else r.init

let lemma_sel_tot (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel{h `contains` r})
  :Lemma (sel_tot h r == sel h r)
         [SMTPat (sel_tot h r)]
  = ()

(* Update. *)
let upd_condition (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel) (x:a) 
  = ~(contains h r) \/ rel (sel h r) x

abstract let upd_tot (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel{h `contains` r}) (x:a{upd_condition h r x}) :Tot heap
  = { h with memory = (fun r' -> if r.addr = r'
			      then Some (| a, (x , rel) |)
                              else h.memory r') }

abstract let upd (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel) (x:a{upd_condition h r x}) :GTot heap
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r)
    then upd_tot h r x
    else
      if r.addr >= h.next_addr
      then (* alloc at r.addr *)
        { next_addr = r.addr + 1;
          memory    = (fun (r':nat) -> if r' = r.addr
	   		           then Some (| a, (x, rel) |)
                                   else h.memory r') }
      else (* strong update at r.addr *)
        { h with memory = (fun r' -> if r' = r.addr
				  then Some (| a, (x, rel) |)
                                  else h.memory r') }

let lemma_upd_tot (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel{h `contains` r}) (x:a{upd_condition h r x})
  :Lemma (upd_tot h r x == upd h r x)
         [SMTPat (upd_tot h r x)]
  = ()


(* Allocate. *)
private abstract let alloc_ref (#a:Type) (h:heap) (x:a) (rel:preorder a) (mm:bool) 
                               (r:mref a rel{~(contains h r) /\ r.addr = h.next_addr /\ r.init == x /\ r.mm == mm}) :Tot heap
  = { next_addr = r.addr + 1;
      memory    = (fun (r':nat) -> if r' = r.addr
	                           then Some (| a, (x, rel) |)
				   else h.memory r')}

abstract let alloc_tot (#a:Type) (h:heap) (x:a) (rel:preorder a) (mm:bool) :Tot (mref a rel * heap)
  = let r = { addr = h.next_addr; init = x; mm = mm } in
    r, alloc_ref h x rel mm r

abstract let alloc (#a:Type) (h:heap) (x:a) (rel:preorder a) (mm:bool) :GTot (mref a rel * heap)
  = let r = { addr = h.next_addr; init = x; mm = mm } in
    r, upd #a #rel h r x

let lemma_alloc_tot (#a:Type) (h:heap) (x:a) (rel:preorder a) (mm:bool) 
  :Lemma (alloc_tot h x rel mm == alloc h x rel mm)
         [SMTPat (alloc_tot h x rel mm)]
  = ()

abstract let free_mm (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel{h `contains` r /\ is_mm r})
  :GTot heap
  = { h with memory = (fun r' -> if r' = r.addr then None else h.memory r') }

let modifies (s:set nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)}
                         ((~ (mem (addr_of r) s)) /\ h0 `contains` r) ==> sel h1 r == sel h0 r) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (contains h1 r)}
                        h0 `contains` r ==> h1 `contains` r)

(** some lemmas that summarize the behavior **)

(*
 * update of a well-typed reference
 *)
private let lemma_upd_contains_test
  (#a:Type) (#rel:preorder a) (h0:heap) (r:mref a rel) (x:a{upd_condition h0 r x})
  :Lemma (h0 `contains` r ==>
          (let h1 = upd h0 r x in
           (forall (b:Type) (rel':preorder b) (r':mref b rel'). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (rel':preorder b) (r':mref b rel'). h0 `contains` r' <==> h1 `contains` r')             /\
	   (forall (b:Type) (rel':preorder b) (r':mref b rel'). r' `unused_in` h0  <==> r' `unused_in` h1)))
  = ()

(*
 * update of a reference that is mapped but not necessarily well-typed
 * we cannot prove that h0 `contains` r' ==> h1 `contains` r'
 * because consider that in h0 (r:ref a) contains (| b, y:b |),
 * and that (r':ref b) s.t. r'.addr = r.addr
 * in h0, r' is well-typed, but in h1 it's not
 *)
private let lemma_upd_contains_not_necessarily_well_typed_test
  (#a:Type) (#rel:preorder a) (h0:heap) (r:mref a rel) (x:a{upd_condition h0 r x})
  :Lemma ((~ (r `unused_in` h0)) ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (rel':preorder b) (r':mref b rel'). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')           /\
	   (forall (b:Type) (rel':preorder b) (r':mref b rel'). (r'.addr <> r.addr /\ h0 `contains` r') ==> h1 `contains` r') /\
	   (forall (b:Type) (rel':preorder b) (r':mref b rel'). r' `unused_in` h0 <==> r' `unused_in` h1)))
  = ()

(*
 * update of an unused reference
 *)
private let lemma_upd_unused_test
  (#a:Type) (#rel:preorder a) (h0:heap) (r:mref a rel) (x:a{upd_condition h0 r x})
  :Lemma (r `unused_in` h0 ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (rel':preorder b) (r':mref b rel'). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (rel':preorder b) (r':mref b rel'). h0 `contains` r' ==> h1 `contains` r')             /\
	   (forall (b:Type) (rel':preorder b) (r':mref b rel'). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1))))
  = ()

(*
 * alloc and alloc_mm behaves just like upd of an unmapped reference
 *)
private let lemma_alloc_test (#a:Type) (h0:heap) (x:a) (rel:preorder a) (mm:bool)
  :Lemma (let (r, h1) = alloc h0 x rel mm in
          r `unused_in` h0 /\
	  h1 `contains` r  /\
          is_mm r = mm     /\
          (forall (b:Type) (rel':preorder b) (r':mref b rel'). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
          (forall (b:Type) (rel':preorder b) (r':mref b rel'). h0 `contains` r' ==> h1 `contains` r')             /\
	  (forall (b:Type) (rel':preorder b) (r':mref b rel'). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1)))
  = ()

private let lemma_free_mm_test (#a:Type) (#rel:preorder a) (h0:heap) (r:mref a rel{h0 `contains` r /\ is_mm r})
  :Lemma (let h1 = free_mm h0 r in
          r `unused_in` h1 /\
	  (forall (b:Type) (rel':preorder b) (r':mref b rel'). addr_of r' <> addr_of r ==>
	                          ((sel h0 r' == sel h1 r'                 /\
				   (h0 `contains` r' <==> h1 `contains` r') /\
				   (r' `unused_in` h0 <==> r' `unused_in` h1)))))
  = ()

private let lemma_upd_modifies_test (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel{h `contains` r \/ r `unused_in` h}) (x:a{rel (sel h r) x})
  :Lemma (modifies (Set.singleton (addr_of r)) h (upd h r x))
  = ()

private let lemma_alloc_fresh_test (#a:Type) (#rel:preorder a) (h0:heap) (x:a) (mm:bool)
  :Lemma (let r, h1 = alloc h0 x rel mm in
          fresh r h0 h1 /\ modifies empty h0 h1)
  = ()

private let lemma_modifies_trans_test (h1:heap) (h2:heap) (h3:heap) (s1:set nat) (s2:set nat)
  :Lemma (requires (modifies s1 h1 h2 /\ modifies s2 h2 h3))
         (ensures  (modifies (union s1 s2) h1 h3))
  = ()  

(** **)

let lemma_contains_implies_used
  (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel)
  :Lemma (requires (h `contains` r))
         (ensures  (~ (r `unused_in` h)))
	 [SMTPatOr [[SMTPat (h `contains` r)]; [SMTPat (r `unused_in` h)]]]
  = ()

let lemma_distinct_addrs_distinct_types
  (#a:Type) (#b:Type) (#rela:preorder a) (#relb:preorder b) (h:heap) (r1:mref a rela) (r2:mref b relb)
  :Lemma (requires (a =!= b /\ h `contains` r1 /\ h `contains` r2))
         (ensures  (addr_of r1 <> addr_of r2))
	 [SMTPatT (h `contains` r1); SMTPatT (h `contains` r2)]
  = ()

let lemma_distinct_addrs_unused
  (#a:Type) (#b:Type) (#rela:preorder a) (#relb:preorder b) (h:heap) (r1:mref a rela) (r2:mref b relb)
  :Lemma (requires (r1 `unused_in` h /\ ~ (r2 `unused_in` h)))
         (ensures  (addr_of r1 <> addr_of r2))
         [SMTPat (r1 `unused_in` h); SMTPat (r2 `unused_in` h)]
  = ()

let lemma_alloc (#a:Type) (#rel:preorder a) (h0:heap) (x:a) (mm:bool)
  :Lemma (requires True)
         (ensures  (let r, h1 = alloc h0 x rel mm in
                    h1 == upd h0 r x /\ fresh r h0 h1 /\ is_mm r = mm))
	 [SMTPat (alloc h0 x rel mm)]
  = ()

let lemma_free_mm_sel (#a:Type) (#b:Type) (h0:heap) (#rela:preorder a) (#relb:preorder b) (r:mref a rela{h0 `contains` r /\ is_mm r}) (r':mref b relb)
  :Lemma (requires True)
         (ensures  (addr_of r' <> addr_of r ==> sel h0 r' == sel (free_mm h0 r) r'))
	 [SMTPat (sel (free_mm h0 r) r')]
  = ()

let lemma_free_mm_unused (#a:Type) (#rel:preorder a) (h0:heap) (r:mref a rel{h0 `contains` r /\ is_mm r})
  :Lemma (requires True)
         (ensures  (r `unused_in` (free_mm h0 r)))
	 [SMTPat (r `unused_in` (free_mm h0 r))]
  = ()

let lemma_free_mm_contains (#a:Type) (#b:Type) (#rela:preorder a) (#relb:preorder b) (h0:heap) (r:mref a rela{h0 `contains` r /\ is_mm r}) (r':mref b relb)
  :Lemma (requires True)
         (ensures  (let h1 = free_mm h0 r in
	            (addr_of r' <> addr_of r /\ h0 `contains` r') ==> h1 `contains` r'))
	 [SMTPat ((free_mm h0 r) `contains` r')]
  = ()

let lemma_sel_same_addr (#a:Type) (#rel:preorder a) (h:heap) (r1:mref a rel) (r2:mref a rel)
  :Lemma (requires (h `contains` r1 /\ addr_of r1 = addr_of r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
	 [SMTPat (sel h r1); SMTPat (sel h r2)]
  = ()

let sel_upd1 (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel) (x:a{upd_condition h r x}) (r':mref a rel)
  :Lemma (requires (addr_of r = addr_of r'))
         (ensures  (sel (upd h r x) r' == x))
         [SMTPat (sel (upd h r x) r')]

  = ()

let sel_upd2 (#a:Type) (#b:Type) (#rela:preorder a) (#relb:preorder b) (h:heap) (r1:mref a rela) (r2:mref b relb) (x:b{upd_condition h r2 x})
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  (sel (upd h r2 x) r1 == sel h r1))
	 [SMTPat (sel (upd h r2 x) r1)]
  = ()

let equal_dom (h1:heap) (h2:heap) :GTot Type0 =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). r `unused_in` h1 <==> r `unused_in` h2

(* Empty. *)
let emp :heap = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

let in_dom_emp (#a:Type) (#rel:preorder a) (r:mref a rel)
  :Lemma (requires True)
         (ensures  (r `unused_in` emp))
	 [SMTPat (r `unused_in` emp)]
  = ()

let upd_contains_a_well_typed (#a:Type) (#b:Type) (#rela:preorder a) (#relb:preorder b) (h:heap) (r:mref a rela) (x:a{upd_condition h r x}) (r':mref b relb)
  :Lemma (requires True)
         (ensures  (((upd h r x) `contains` r) /\

	            ((h `contains` r' /\  //if h contains_a_well_typed r' and

                      ((h `contains` r) \/  //either h contains_a_well_typed r
		       (r `unused_in` h) \/  //or h does not contain r
		       (addr_of r <> addr_of r')))  //or r'.addr <> r.addr
		     ==> (upd h r x) `contains` r')))  //then updated heap contains_a_well_typed r'
         [SMTPat ((upd h r x) `contains` r')]
  = ()

abstract let equal (h1:heap) (h2:heap) :Type0 =
  h1.next_addr = h2.next_addr /\
  FStar.FunctionalExtensionality.feq h1.memory h2.memory

val equal_extensional: h1:heap -> h2:heap
                       -> Lemma (requires True) (ensures (equal h1 h2 <==> h1 == h2))
		         [SMTPat (equal h1 h2)]
let equal_extensional h1 h2 = ()

let upd_upd_same_ref (#a:Type) (#rel:preorder a) (h:heap) (r:mref a rel) (x:a{rel (sel h r) x}) (y:a{rel x y})
  :Lemma (requires True)
         (ensures  (upd (upd h r x) r y == upd h r y))
	 [SMTPat (upd (upd h r x) r y)]
  = assert (equal (upd (upd h r x) r y) (upd h r y))


val op_Hat_Plus_Plus: #a:Type -> #rel:preorder a -> r:mref a rel -> set nat -> GTot (set nat)
let op_Hat_Plus_Plus #a #rel r s = union (only r) s

val op_Plus_Plus_Hat: #a:Type -> #rel:preorder a -> set nat -> r:mref a rel -> GTot (set nat)
let op_Plus_Plus_Hat #a #rel s r = union s (only r)

val op_Hat_Plus_Hat: #a:Type -> #b:Type -> #rela:preorder a -> #relb:preorder b -> mref a rela -> mref b relb -> GTot (set nat)
let op_Hat_Plus_Hat #a #b #rela #relb r1 r2 = union (only r1) (only r2)


(** some lemmas about the types and relations of references with the same address **)

let lemma_contains_same_type (#a:Type) (#b:Type) (#rel:preorder a) (#rel':preorder b) (h:heap) (r:mref a rel{h `contains` r}) (r':mref b rel'{h `contains` r'})
  :Lemma (addr_of r = addr_of r' ==> a == b)
  = ()

let lemma_contains_same_rel (#a:Type) (#b:Type) (#rel:preorder a) (#rel':preorder b) (h:heap) (r:mref a rel{h `contains` r}) (r':mref b rel'{h `contains` r'})
  :Lemma (addr_of r = addr_of r' ==> rel === rel')
  = ()
