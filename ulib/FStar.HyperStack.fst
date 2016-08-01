module FStar.HyperStack
open FStar.HyperHeap
module M  = FStar.Map
module HH = FStar.HyperHeap

inline let is_in (r:rid) (h:HH.t) = h `Map.contains` r

assume val color: rid -> Tot int //TODO: enrich FStar.HyperHeap with this
let is_stack_region r = color r > 0
let is_eternal_region r  = color r <= 0
type sid = r:rid{is_stack_region r} //stack region ids
let is_above r1 r2 = r1 `includes` r2
let is_just_below r1 r2 = r1 `extends` r2
let is_below r1 r2 = r2 `is_above` r1
assume Root_is_eternal: is_eternal_region HH.root

let downward_closed (h:HH.t) = 
  forall (r:rid). r=HH.root \/ (forall (s:rid). r `is_above` s ==> (is_stack_region r <==> is_stack_region s))

abstract let is_tip (tip:HH.rid) (h:HH.t) = 
  (is_stack_region tip \/ tip=HH.root)                                  //the tip is a stack region, or the root
  /\ tip `is_in` h                                                      //the tip is active
  /\ (forall (r:sid). r `is_in` h ==> r `is_above` tip)                      //any other sid activation is a parent of the tip
  /\ (forall (r:rid). r `is_above` tip ==> r=HH.root \/ is_stack_region r)    //and every parent of tip is a stack region, except if it is the root
  /\ (forall (r:rid{tip<>HH.root}). r `is_below` tip                                      //if tip is a stack region, then no region beyond the tip
			     \/ (is_stack_region r /\ HH.disjoint r tip)             //             or any stack region disjoint from the tip
		==> not (Map.contains h r))                            //is in the heap

noeq abstract type mem =
  | HS : h:HH.t{HH.root `is_in` h /\ HH.map_invariant h /\ downward_closed h}        //the memory itself, always contains the root region, and the parent of any active region is active
       -> tip:rid{tip `is_tip` h}                                                   //the id of the current top-most region
       -> mem

//A (reference a) may reside in the stack or heap
noeq type reference (a:Type) =
  | MkRef : id:rid -> ref:HH.rref id a -> reference a

let live_region (m:mem) (i:rid) =
  (is_eternal_region i \/ i `is_above` m.tip)
  /\ Map.contains m.h i
  
let contains (#a:Type) (m:mem) (s:reference a) =
  live_region m s.id
  /\ HH.contains_ref s.ref m.h

let upd (#a:Type) (m:mem) (s:reference a{live_region m s.id}) (v:a)
  : Tot mem
  = HS (m.h.[s.ref] <- v) m.tip

let sel (#a:Type) (m:mem) (s:reference a)
  : Tot a
  = m.h.[s.ref]

let equal_domains (m0:mem) (m1:mem) =
  m0.tip = m1.tip
  /\ Set.equal (Map.domain m0.h) (Map.domain m1.h)
  /\ (forall r. Map.contains m0.h r ==> TSet.equal (Heap.domain (Map.sel m0.h r)) (Heap.domain (Map.sel m1.h r)))

let lemma_equal_domains_trans (m0:mem) (m1:mem) (m2:mem) : Lemma
  (requires (equal_domains m0 m1 /\ equal_domains m1 m2))
  (ensures  (equal_domains m0 m2))
  [SMTPat (equal_domains m0 m1); SMTPat (equal_domains m1 m2)]
  = ()

let top_frame (m:mem) = Map.sel m.h m.tip
  
let fresh_frame (m0:mem) (m1:mem) =
  not (Map.contains m0.h m1.tip)
  /\ HH.parent m1.tip = m0.tip
  /\ m1.h == Map.upd m0.h m1.tip Heap.emp

let poppable m = m.tip <> HH.root

let remove_elt (#a:eqtype) (s:Set.set a) (x:a) = Set.intersect s (Set.complement (Set.singleton x))

let popped m0 m1 =
  poppable m0
  /\ HH.parent m0.tip = m1.tip
  /\ Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip)
  /\ Map.equal m1.h (Map.restrict (Map.domain m1.h) m0.h)

let test (r:rid) (s:rid) = 
  assert (r `is_below` s ==> s `is_above` r)
  
let pop (m0:mem{poppable m0}) : Tot mem =
  let dom = remove_elt (Map.domain m0.h) m0.tip in
  let h0 = m0.h in
  let h1 = Map.restrict dom m0.h in
  let tip0 = m0.tip in
  let tip1 = HH.parent tip0 in
  HS h1 tip1
  
let lemma_pop_is_popped (m0:mem{poppable m0})
  : Lemma (popped m0 (pop m0))
  = let m1 = pop m0 in
    assert (Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip))

type s_ref (i:rid) (a:Type) = s:reference a{s.id = i}

let frameOf #a (s:reference a) = s.id

let modifies (s:Set.set rid) (m0:mem) (m1:mem) =
  HH.modifies_just s m0.h m1.h
  /\ m0.tip=m1.tip
let as_ref #a (x:reference a) : Tot (Heap.ref a) = HH.as_ref #a #x.id x.ref
let as_aref #a (x:reference a) : Tot Heap.aref = Heap.Ref (HH.as_ref #a #x.id x.ref)
let modifies_one id h0 h1 = HH.modifies_one id h0.h h1.h
let modifies_ref (id:rid) (s:TSet.set Heap.aref) (h0:mem) (h1:mem) =
  HH.modifies_rref id s h0.h h1.h /\ h1.tip=h0.tip

let lemma_upd_1 #a (h:mem) (x:reference a) (v:a) : Lemma
  (requires (contains h x))
  (ensures (contains h x
	    /\ modifies_one (frameOf x) h (upd h x v)
	    /\ modifies_ref (frameOf x) (TSet.singleton (as_aref x)) h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPatT (contains h x)]
  = ()

let lemma_upd_2 #a (h:mem) (x:reference a) (v:a) : Lemma
  (requires (~(contains h x) /\ frameOf x = h.tip))
  (ensures (~(contains h x)
	    /\ frameOf x = h.tip
	    /\ modifies_one h.tip h (upd h x v)
	    /\ modifies_ref h.tip TSet.empty h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPatT (~(contains h x))]
  = ()

val lemma_live_1: #a:Type ->  #a':Type -> h:mem -> x:reference a -> x':reference a' -> Lemma
  (requires (contains h x /\ ~(contains h x')))
  (ensures  (x.id <> x'.id \/ ~ (as_ref x === as_ref x')))
  [SMTPat (contains h x); SMTPat (~(contains h x'))]
let lemma_live_1 #a #a' h x x' = ()
