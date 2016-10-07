module FStar.HyperStack
open FStar.HyperHeap
module M  = FStar.Map
module HH = FStar.HyperHeap

let is_in (r:rid) (h:HH.t) = h `Map.contains` r

let is_stack_region r = color r > 0
let is_eternal_color c = c <= 0
let is_eternal_region r  = is_eternal_color (color r)

type sid = r:rid{is_stack_region r} //stack region ids

let is_above r1 r2      = r1 `includes` r2
let is_just_below r1 r2 = r1 `extends`  r2
let is_below r1 r2      = r2 `is_above` r1
let is_strictly_below r1 r2 = r1 `is_below` r2 && r1<>r2
let is_strictly_above r1 r2 = r1 `is_above` r2 && r1<>r2

let downward_closed (h:HH.t) = 
  forall (r:rid). r `is_in` h  //for any region in the memory
        ==> (r=HH.root    //either is the root
	    \/ (forall (s:rid). r `is_above` s  //or, any region beneath it
			  /\ s `is_in` h   //that is also in the memory
		     ==> (is_stack_region r = is_stack_region s))) //must be of the same flavor as itself

let is_tip (tip:HH.rid) (h:HH.t) = 
  (is_stack_region tip \/ tip=HH.root)                                  //the tip is a stack region, or the root
  /\ tip `is_in` h                                                      //the tip is active
  /\ (forall (r:sid). r `is_in` h <==> r `is_above` tip)                      //any other sid activation is a above (or equal to) the tip

let hh = h:HH.t{HH.root `is_in` h /\ HH.map_invariant h /\ downward_closed h}        //the memory itself, always contains the root region, and the parent of any active region is active

noeq type mem =
  | HS : h:hh
       -> tip:rid{tip `is_tip` h}                                                   //the id of the current top-most region
       -> mem

let empty_mem (m:HH.t) = 
  let empty_map = Map.restrict (Set.empty) m in 
  let h = Map.upd empty_map HH.root Heap.emp in 
  let tip = HH.root in 
  HS h tip
 
let test0 (m:mem) (r:rid{r `is_above` m.tip}) = 
    assert (r `is_in` m.h)

let test1 (m:mem) (r:rid{r `is_above` m.tip}) = 
    assert (r=HH.root \/ is_stack_region r)

let test2 (m:mem) (r:sid{m.tip `is_above` r /\ m.tip <> r}) =  
   assert (~ (r `is_in` m.h))

let dc_elim (h:HH.t{downward_closed h}) (r:rid{r `is_in` h /\ r <> HH.root}) (s:rid)
  : Lemma (r `is_above` s /\ s `is_in` h ==> is_stack_region r = is_stack_region s)
  = ()	  

let test3 (m:mem) (r:rid{r <> HH.root /\ is_eternal_region r /\ m.tip `is_above` r /\ is_stack_region m.tip})
  : Lemma (~ (r `is_in` m.h))
  = root_has_color_zero()

let test4 (m:mem) (r:rid{r <> HH.root /\ is_eternal_region r /\ r `is_above` m.tip /\ is_stack_region m.tip})
  : Lemma (~ (r `is_in` m.h))
  = ()

let eternal_region_does_not_overlap_with_tip (m:mem) (r:rid{is_eternal_region r /\ not (HH.disjoint r m.tip) /\ r<>HH.root /\ is_stack_region m.tip})
  : Lemma (requires True)
	  (ensures (~ (r `is_in` m.h)))
  = root_has_color_zero()

let poppable m = m.tip <> HH.root

let remove_elt (#a:eqtype) (s:Set.set a) (x:a) = Set.intersect s (Set.complement (Set.singleton x))

let popped m0 m1 =
  poppable m0
  /\ HH.parent m0.tip = m1.tip
  /\ Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip)
  /\ Map.equal m1.h (Map.restrict (Map.domain m1.h) m0.h)

let pop (m0:mem{poppable m0}) : GTot mem =
  root_has_color_zero();
  let dom = remove_elt (Map.domain m0.h) m0.tip in
  let h0 = m0.h in
  let h1 = Map.restrict dom m0.h in
  let tip0 = m0.tip in
  let tip1 = HH.parent tip0 in
  assert (forall (r:sid). Map.contains h1 r ==>
  	    (forall (s:sid). includes s r ==> Map.contains h1 s));
  HS h1 tip1

//A (reference a) may reside in the stack or heap, and may be manually managed
noeq type reference (a:Type) =
  | MkRef : id:rid -> mm:bool -> ref:HH.rref id a -> reference a

//adding (not s.mm) to stackref and ref so as to keep their semantics as is
let stackref (a:Type) = s:reference a { is_stack_region s.id && not s.mm }
let ref (a:Type) = s:reference a{is_eternal_region s.id && not s.mm}

let mmstackref (a:Type) = s:reference a {is_stack_region s.id && s.mm }
let mmref (a:Type) = s:reference a{is_eternal_region s.id && s.mm}

let live_region (m:mem) (i:rid) =
  (is_eternal_region i \/ i `is_above` m.tip)
  /\ Map.contains m.h i
  
let contains (#a:Type) (m:mem) (s:reference a) =
  live_region m s.id
  /\ HH.contains_ref s.ref m.h

let upd (#a:Type) (m:mem) (s:reference a{live_region m s.id}) (v:a)
  : GTot mem
  = HS (m.h.[s.ref] <- v) m.tip

let sel (#a:Type) (m:mem) (s:reference a)
  : GTot a
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

let equal_stack_domains (m0:mem) (m1:mem) =
  m0.tip = m1.tip
  /\ (forall r. (is_stack_region r /\ r `is_above` m0.tip) ==> TSet.equal (Heap.domain (Map.sel m0.h r)) (Heap.domain (Map.sel m1.h r)))

let lemma_equal_stack_domains_trans (m0:mem) (m1:mem) (m2:mem) : Lemma
  (requires (equal_stack_domains m0 m1 /\ equal_stack_domains m1 m2))
  (ensures  (equal_stack_domains m0 m2))
  [SMTPat (equal_stack_domains m0 m1); SMTPat (equal_stack_domains m1 m2)]
  = ()

let modifies (s:Set.set rid) (m0:mem) (m1:mem) =
  HH.modifies_just s m0.h m1.h
  /\ m0.tip=m1.tip

let modifies_transitively (s:Set.set rid) (m0:mem) (m1:mem) =
  HH.modifies s m0.h m1.h
  /\ m0.tip=m1.tip

let heap_only (m0:mem) =
  m0.tip = HH.root

let top_frame (m:mem) = Map.sel m.h m.tip
  
let fresh_frame (m0:mem) (m1:mem) =
  not (Map.contains m0.h m1.tip)
  /\ HH.parent m1.tip = m0.tip
  /\ m1.h == Map.upd m0.h m1.tip Heap.emp

let lemma_pop_is_popped (m0:mem{poppable m0})
  : Lemma (popped m0 (pop m0))
  = let m1 = pop m0 in
    assert (Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip))

type s_ref (i:rid) (a:Type) = s:reference a{s.id = i}

let frameOf #a (s:reference a) = s.id

let as_ref #a (x:reference a)  : GTot (Heap.ref a) = HH.as_ref #a #x.id x.ref
let as_aref #a (x:reference a) : GTot Heap.aref = Heap.Ref (HH.as_ref #a #x.id x.ref)
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

let above_tip_is_live (#a:Type) (m:mem) (x:reference a) : Lemma
  (requires (x.id `is_above` m.tip))
  (ensures (x.id `is_in` m.h))
  = ()
