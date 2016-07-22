module FStar.SGX
open FStar.HyperHeap
module HH = FStar.HyperHeap

let is_above r1 r2 = HH.includes r1 r2
let is_below r1 r2 = HH.extends r1 r2

let is_tip (tip:HH.rid) (h:HH.t) = 
  Map.contains h tip                                          //the tip is active
  /\ (forall r. Map.contains h r ==> is_above r tip)             //any other activation is a parent of the tip
  /\ (forall r. is_below r tip \/ HH.disjoint r tip ==> not (Map.contains h r))        //nothing beyond or disjoint from the tip is active

noeq type mem =
  | HS : h:HH.t{Map.contains h HH.root /\ HH.map_invariant h} //the memory itself, always contains the root region  
       -> tip:HH.rid{is_tip tip h}                             //the id of the current top-most stack frame
       -> mem

noeq type stackref (a:Type) =
  | MkStacked : id:rid -> ref:HH.rref id a -> stackref a

let contains (#a:Type) (m:mem) (s:stackref a) = 
  is_above s.id m.tip
  /\ Map.contains m.h s.id
  /\ HH.contains_ref s.ref m.h

let upd (#a:Type) (m:mem) (s:stackref a{is_above s.id m.tip}) (v:a) 
  : Tot mem 
  = HS (HH.upd m.h s.ref v) m.tip

let sel (#a:Type) (m:mem) (s:stackref a)
  : Tot a 
  = HH.sel m.h s.ref

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

let pop (m0:mem{poppable m0}) : Tot mem =
  let dom = remove_elt (Map.domain m0.h) m0.tip in
  let h1 = Map.restrict dom m0.h in
  let tip0 = m0.tip in
  let tip1 = HH.parent tip0 in
  assert (forall r. is_above r tip0 ==> r=tip0 \/ is_above r tip1);
  HS h1 tip1

let lemma_pop_is_popped (m0:mem{poppable m0})
  : Lemma (popped m0 (pop m0))
  = let m1 = pop m0 in 
    assert (Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip))

type s_ref (i:rid) (a:Type) = s:stackref a{s.id = i}

let frameOf #a (s:stackref a) = s.id

let modifies (s:Set.set rid) (m0:mem) (m1:mem) =
  HH.modifies s m0.h m1.h
  /\ m0.tip=m1.tip

let as_ref #a (x:stackref a) : Tot (Heap.ref a) = HH.as_ref #a #x.id x.ref
let as_aref #a (x:stackref a) : Tot Heap.aref = Heap.Ref (HH.as_ref #a #x.id x.ref)
let modifies_one id h0 h1 = HH.modifies_one id h0.h h1.h
let modifies_ref (id:rid) (s:TSet.set Heap.aref) (h0:mem) (h1:mem) =
  HH.modifies_rref id s h0.h h1.h /\ h1.tip=h0.tip

let lemma_upd_1 #a (h:mem) (x:stackref a) (v:a) : Lemma
  (requires (contains h x))
  (ensures (contains h x
	    /\ modifies_one (frameOf x) h (upd h x v)
	    /\ modifies_ref (frameOf x) (TSet.singleton (as_aref x)) h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPatT (contains h x)]
  = ()

let lemma_upd_2 #a (h:mem) (x:stackref a) (v:a) : Lemma
  (requires (~(contains h x) /\ frameOf x = h.tip))
  (ensures (~(contains h x)
	    /\ frameOf x = h.tip
	    /\ modifies_one h.tip h (upd h x v)
	    /\ modifies_ref h.tip TSet.empty h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPatT (~(contains h x))]
  = ()

assume val lemma_live_1: #a:Type ->  #a':Type -> h:mem -> x:stackref a -> x':stackref a' -> Lemma
  (requires (contains h x /\ ~(contains h x')))
  (ensures  (Heap.Ref (as_ref x) =!= Heap.Ref (as_ref x')))
  [SMTPat (contains h x); SMTPatT (~(contains h x'))]

