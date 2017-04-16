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
  | MkRef : id:rid -> ref:HH.rref id a -> reference a

let is_mm (#a:Type) (r:reference a) :GTot bool = HH.is_mm r.ref

//adding (not s.mm) to stackref and ref so as to keep their semantics as is
let stackref (a:Type) = s:reference a { is_stack_region s.id && not (is_mm s) }
let ref (a:Type) = s:reference a{is_eternal_region s.id && not (is_mm s)}

let mmstackref (a:Type) = s:reference a {is_stack_region s.id && is_mm s }
let mmref (a:Type) = s:reference a{is_eternal_region s.id && is_mm s}

(*
 * The Map.contains conjunct is necessary to prove that upd
 * returns a valid mem. In particular, without Map.contains,
 * we cannot prove the eternal regions invariant that all
 * included regions of a region are also in the map.
 *)
let live_region (m:mem) (i:rid) =
  (is_eternal_region i \/ i `is_above` m.tip)
  /\ Map.contains m.h i

(*
 * AR: adding a weaker version of live_region that could be
 * used in the precondition of read.
 *)
let weak_live_region (m:mem) (i:rid) =
  is_eternal_region i \/ i `is_above` m.tip

let contains (#a:Type) (m:mem) (s:reference a) =
  live_region m s.id
  /\ HH.contains_ref s.ref m.h

let unused_in (#a:Type) (r:reference a) (h:mem) =
  ~ (live_region h r.id) \/
  HH.unused_in r.ref h.h

private val weak_live_region_implies_eternal_or_in_map: r:rid -> m:mem -> Lemma
  (requires (weak_live_region m r))
  (ensures (is_eternal_region r \/ Map.contains m.h r))
let weak_live_region_implies_eternal_or_in_map r m = ()

(*
 * AR: corresponding to weak_live_region above.
 * Replacing HH.contains_ref with weak_contains_ref under mm flag.
 * If the reference is manually managed, we must prove Heap.contains
 * before reading the ref.
 *)
let weak_contains (#a:Type) (m:mem) (s:reference a) =
  weak_live_region m s.id /\
  (if is_mm s then HH.weak_contains_ref s.ref m.h else True)

let upd (#a:Type) (m:mem) (s:reference a{live_region m s.id}) (v:a)
  : GTot mem
  = HS (m.h.[s.ref] <- v) m.tip

(*
 * AR: why is this not enforcing live_region ?
 *)
let sel (#a:Type) (m:mem) (s:reference a)
  : GTot a
  = m.h.[s.ref]

let equal_domains (m0:mem) (m1:mem) =
  m0.tip = m1.tip
  /\ Set.equal (Map.domain m0.h) (Map.domain m1.h)
  /\ (forall r. Map.contains m0.h r ==> Heap.equal_dom (Map.sel m0.h r) (Map.sel m1.h r))

let lemma_equal_domains_trans (m0:mem) (m1:mem) (m2:mem) : Lemma
  (requires (equal_domains m0 m1 /\ equal_domains m1 m2))
  (ensures  (equal_domains m0 m2))
  [SMTPat (equal_domains m0 m1); SMTPat (equal_domains m1 m2)]
  = ()

let equal_stack_domains (m0:mem) (m1:mem) =
  m0.tip = m1.tip
  /\ (forall r. (is_stack_region r /\ r `is_above` m0.tip) ==> Heap.equal_dom (Map.sel m0.h r) (Map.sel m1.h r))

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

let modifies_drop_tip (m0:mem) (m1:mem) (m2:mem) (s:Set.set rid)
    : Lemma (fresh_frame m0 m1 /\
	     modifies_transitively (Set.union s (Set.singleton m1.tip)) m1 m2 ==> 
	     modifies_transitively s m0 (pop m2))
    = ()

let lemma_pop_is_popped (m0:mem{poppable m0})
  : Lemma (popped m0 (pop m0))
  = let m1 = pop m0 in
    assert (Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip))

type s_ref (i:rid) (a:Type) = s:reference a{s.id = i}

let frameOf #a (s:reference a) = s.id

let as_ref #a (x:reference a)  : GTot (Heap.ref a) = HH.as_ref #a #x.id x.ref
let as_addr #a (x:reference a) : GTot nat = Heap.addr_of (HH.as_ref #a #x.id x.ref)
let modifies_one id h0 h1 = HH.modifies_one id h0.h h1.h
let modifies_ref (id:rid) (s:Set.set nat) (h0:mem) (h1:mem) =
  HH.modifies_rref id s h0.h h1.h /\ h1.tip=h0.tip

let lemma_upd_1 #a (h:mem) (x:reference a) (v:a) : Lemma
  (requires (contains h x))
  (ensures (contains h x
	    /\ modifies_one (frameOf x) h (upd h x v)
	    /\ modifies_ref (frameOf x) (Set.singleton (as_addr x)) h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPatT (contains h x)]
  = ()

let lemma_upd_2 (#a:Type) (h:mem) (x:reference a) (v:a) : Lemma
  (requires (frameOf x = h.tip /\ x `unused_in` h))
  (ensures (frameOf x = h.tip
	    /\ modifies_one h.tip h (upd h x v)
	    /\ modifies_ref h.tip Set.empty h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPatT (x `unused_in` h)]
  = ()

val lemma_live_1: #a:Type ->  #a':Type -> h:mem -> x:reference a -> x':reference a' -> Lemma
  (requires (contains h x /\ x' `unused_in` h))
  (ensures  (x.id <> x'.id \/ ~ (as_ref x === as_ref x')))
  [SMTPat (contains h x); SMTPat (x' `unused_in` h)]
let lemma_live_1 #a #a' h x x' = ()

let above_tip_is_live (#a:Type) (m:mem) (x:reference a) : Lemma
  (requires (x.id `is_above` m.tip))
  (ensures (x.id `is_in` m.h))
  = ()

(*
 * AR: relating contains and weak_contains.
 *)
let contains_implies_weak_contains (#a:Type) (h:mem) (x:reference a) :Lemma
  (requires (True))
  (ensures (contains h x ==> weak_contains h x))
  [SMTPatOr [[SMTPat (contains h x)]; [SMTPat (weak_contains h x)]] ]
  = ()

noeq type some_ref =
| Ref : #a:Type0 -> reference a -> some_ref

let some_refs = list some_ref

let rec regions_of_some_refs (rs:some_refs) : Tot (Set.set rid) = 
  match rs with
  | [] -> Set.empty
  | (Ref r)::tl -> Set.union (Set.singleton r.id) (regions_of_some_refs tl)

let rec refs_in_region (r:rid) (rs:some_refs) : GTot (Set.set nat) =
  match rs with
  | []         -> Set.empty
  | (Ref x)::tl ->
    Set.union (if x.id=r then Set.singleton (as_addr x) else Set.empty)
               (refs_in_region r tl)

unfold let mods (rs:some_refs) h0 h1 =
    modifies (normalize_term (regions_of_some_refs rs)) h0 h1
  /\ (forall (r:rid). modifies_ref r (normalize_term (refs_in_region r rs)) h0 h1)

////////////////////////////////////////////////////////////////////////////////
let eternal_disjoint_from_tip (h:mem{is_stack_region h.tip})
			      (r:rid{is_eternal_region r /\
				     r<>HH.root /\
				     r `is_in` h.h})
   : Lemma (HH.disjoint h.tip r)
   = ()
   
////////////////////////////////////////////////////////////////////////////////
#set-options "--initial_fuel 0 --max_fuel 0 --log_queries"
let f (a:Type0) (b:Type0) (x:reference a) (x':reference a) 
			  (y:reference b) (z:reference nat) 
			  (h0:mem) (h1:mem) = 
  assume (h0 `contains` x);
  assume (h0 `contains` x');  
  assume (as_addr x <> as_addr x');
  assume (x.id == x'.id);
  assume (x.id <> y.id);
  assume (x.id <> z.id);
  //assert (Set.equal (normalize_term (refs_in_region x.id [Ref x])) (normalize_term (Set.singleton (as_addr x))))
  assume (mods [Ref x; Ref y; Ref z] h0 h1);
  //AR: TODO: this used to be an assert, but this no longer goers through
  //since now we have set of nats, which plays badly with normalize_term
  //on one side it remains nat, on the other side the normalizer normalizes it to a refinement type
  //see for example the assertion above that doesn't succeed
  assume (modifies_ref x.id (Set.singleton (as_addr x)) h0 h1);
  assert (modifies (Set.union (Set.singleton x.id)
  			      (Set.union (Set.singleton y.id)
  					 (Set.singleton z.id))) h0 h1);
  ()


 //--------------------------------------------------------------------------------
  //assert (sel h0 x' == sel h1 x')

(* let f2 (a:Type0) (b:Type0) (x:reference a) (y:reference b) *)
(* 			   (h0:mem) (h1:mem) =  *)
(*   assume (HH.disjoint (frameOf x) (frameOf y)); *)
(*   assume (mods [Ref x; Ref y] h0 h1); *)
(*  //-------------------------------------------------------------------------------- *)
(*   assert (modifies_ref x.id (TSet.singleton (as_aref x)) h0 h1) *)

(* let rec modifies_some_refs (i:some_refs) (rs:some_refs) (h0:mem) (h1:mem) : GTot Type0 = *)
(*   match i with *)
(*   | [] -> True *)
(*   | Ref x::tl -> *)
(*     let r = x.id in *)
(*     (modifies_ref r (normalize_term (refs_in_region r rs)) h0 h1 /\ *)
(*      modifies_some_refs tl rs h0 h1) *)

(* unfold let mods_2 (rs:some_refs) h0 h1 = *)
(*     modifies (normalize_term (regions_of_some_refs rs)) h0 h1 *)
(*   /\ modifies_some_refs rs rs h0 h1 *)

(* #reset-options "--log_queries --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0" *)
(* #set-options "--debug FStar.HyperStack --debug_level print_normalized_terms" *)
(* let f3 (a:Type0) (b:Type0) (x:reference a) *)
(* 			   (h0:mem) (h1:mem) =  *)
(*   assume (mods_2 [Ref x] h0 h1); *)
(*  //-------------------------------------------------------------------------------- *)
(*   assert (modifies_ref x.id (TSet.singleton (as_aref x)) h0 h1) *)
