module FStar.Monotonic.HyperStack

open FStar.Preorder
open FStar.Monotonic.HyperHeap
module M  = FStar.Map
module HH = FStar.Monotonic.HyperHeap

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
noeq type mreference (a:Type) (rel:preorder a) =
  | MkRef : id:rid -> ref:HH.mrref id a rel -> mreference a rel

let is_mm (#a:Type) (#rel:preorder a) (r:mreference a rel) :GTot bool = HH.is_mm r.ref

//adding (not s.mm) to stackref and ref so as to keep their semantics as is
let mstackref (a:Type) (rel:preorder a) = s:mreference a rel{ is_stack_region s.id && not (is_mm s) }
let mref (a:Type) (rel:preorder a) = s:mreference a rel{is_eternal_region s.id && not (is_mm s)}

let mmmstackref (a:Type) (rel:preorder a) = s:mreference a rel{is_stack_region s.id && is_mm s }
let mmmref (a:Type) (rel:preorder a) = s:mreference a rel{is_eternal_region s.id && is_mm s}

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

let contains (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel) =
  live_region m s.id
  /\ HH.contains_ref s.ref m.h

let unused_in (#a:Type) (#rel:preorder a) (r:mreference a rel) (h:mem) =
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
let weak_contains (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel) =
  weak_live_region m s.id /\
  (if is_mm s then HH.weak_contains_ref s.ref m.h else True)

(*
 * AR: why is this not enforcing live_region ?
 *)
let sel (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel)
  : GTot a
  = m.h.[s.ref]

let upd (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel{live_region m s.id}) (v:a)
  : GTot mem
  = HS (m.h.[s.ref] <- v) m.tip

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

type s_mref (i:rid) (a:Type) (rel:preorder a) = s:mreference a rel{s.id = i}

let frameOf #a #rel (s:mreference a rel) = s.id

let as_ref #a #rel (x:mreference a rel)  : GTot (Heap.mref a rel) = HH.as_ref #a #x.id x.ref
let as_addr #a #rel (x:mreference a rel) : GTot nat = Heap.addr_of (HH.as_ref #a #x.id x.ref)
let modifies_one id h0 h1 = HH.modifies_one id h0.h h1.h
let modifies_ref (id:rid) (s:Set.set nat) (h0:mem) (h1:mem) =
  HH.modifies_rref id s h0.h h1.h /\ h1.tip=h0.tip

let lemma_upd_1 #a #rel (h:mem) (x:mreference a rel) (v:a{rel (sel h x) v}) : Lemma
  (requires (contains h x))
  (ensures (contains h x
	    /\ modifies_one (frameOf x) h (upd h x v)
	    /\ modifies_ref (frameOf x) (Set.singleton (as_addr x)) h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPat (contains h x)]
  = ()

let lemma_upd_2 (#a:Type) (#rel:preorder a) (h:mem) (x:mreference a rel) (v:a{rel (sel h x) v}) : Lemma
  (requires (frameOf x = h.tip /\ x `unused_in` h))
  (ensures (frameOf x = h.tip
	    /\ modifies_one h.tip h (upd h x v)
	    /\ modifies_ref h.tip Set.empty h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPat (x `unused_in` h)]
  = ()

val lemma_live_1: #a:Type ->  #a':Type -> #rel:preorder a -> #rel':preorder a'
                  -> h:mem -> x:mreference a rel -> x':mreference a' rel' -> Lemma
  (requires (contains h x /\ x' `unused_in` h))
  (ensures  (x.id <> x'.id \/ ~ (as_ref x === as_ref x')))
  [SMTPat (contains h x); SMTPat (x' `unused_in` h)]
let lemma_live_1 #a #a' #rel #rel' h x x' = ()

let above_tip_is_live (#a:Type) (#rel:preorder a) (m:mem) (x:mreference a rel) : Lemma
  (requires (x.id `is_above` m.tip))
  (ensures (x.id `is_in` m.h))
  = ()

(*
 * AR: we can prove this lemma only if both the mreferences have same preorder
 *)
let lemma_sel_same_addr (#a:Type0) (#rel:preorder a) (h:mem) (r1:mreference a rel) (r2:mreference a rel)
  :Lemma (requires (h `contains` r1 /\ frameOf r1 == frameOf r2 /\ as_addr r1 = as_addr r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
= lemma_sel_same_addr #(frameOf r1) #a #rel h.h r1.ref r2.ref

let lemma_sel_same_addr' (#a:Type0) (#rel:preorder a) (h:mem) (r1:mreference a rel) (r2:mreference a rel)
  :Lemma (requires (h `contains` r1 /\ frameOf r1 == frameOf r2 /\ as_addr r1 = as_addr r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
   [SMTPat (sel h r1); SMTPat (sel h r2)]
= lemma_sel_same_addr h r1 r2

#set-options "--z3rlimit 16"

let lemma_upd_same_addr (#a: Type0) (#rel: preorder a) (h: mem) (r1 r2: mreference a rel) (x: a)
  :Lemma (requires ((h `contains` r1 \/ h `contains` r2) /\ frameOf r1 == frameOf r2 /\ as_addr r1 = as_addr r2))
         (ensures (h `contains` r1 /\ h `contains` r2 /\ upd h r1 x == upd h r2 x))
= Classical.or_elim
    #(h `contains` r1)
    #(h `contains` r2)
    #(fun _ -> h `contains` r1 /\ h `contains` r2)
    (fun _ -> lemma_sel_same_addr h r1 r2)
    (fun _ -> lemma_sel_same_addr h r2 r1);
  lemma_upd_same_addr h.h (MkRef?.ref r1) (MkRef?.ref r2) x

let lemma_upd_same_addr' (#a: Type0) (#rel: preorder a) (h: mem) (r1 r2: mreference a rel) (x: a)
  :Lemma (requires ((h `contains` r1 \/ h `contains` r2) /\ frameOf r1 == frameOf r2 /\ as_addr r1 = as_addr r2))
         (ensures (h `contains` r1 /\ h `contains` r2 /\ upd h r1 x == upd h r2 x))
         [SMTPat (upd h r1 x); SMTPat (upd h r2 x)]
= lemma_upd_same_addr h r1 r2 x

(*
 * AR: relating contains and weak_contains.
 *)
let contains_implies_weak_contains (#a:Type) (#rel:preorder a) (h:mem) (x:mreference a rel) :Lemma
  (requires (True))
  (ensures (contains h x ==> weak_contains h x))
  [SMTPatOr [[SMTPat (contains h x)]; [SMTPat (weak_contains h x)]] ]
  = ()

noeq type some_ref =
| Ref : #a:Type0 -> #rel:preorder a -> mreference a rel -> some_ref

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
#set-options "--initial_fuel 0 --max_fuel 0"
let f (a:Type0) (b:Type0) (rel_a:preorder a) (rel_b:preorder b) (rel_n:preorder nat)
                          (x:mreference a rel_a) (x':mreference a rel_a) 
			  (y:mreference b rel_b) (z:mreference nat rel_n) 
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


(*** Untyped views of references *)

(* Definition and ghost decidable equality *)

noeq abstract type aref: Type0 =
| ARef:
    (aref_region: rid) ->
    (aref_aref: HH.aref aref_region) ->
    aref

abstract let dummy_aref : aref = ARef _ (HH.dummy_aref HH.root)

abstract let aref_equal
  (a1 a2: aref)
: Ghost bool
  (requires True)
  (ensures (fun b -> b == true <==> a1 == a2))
= a1.aref_region = a2.aref_region && HH.aref_equal a1.aref_aref a2.aref_aref

(* Introduction rule *)

abstract let aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
: Tot aref
= ARef r.id (HH.aref_of r.ref)

(* Operators lifted from reference *)

abstract let frameOf_aref
  (a: aref)
: GTot HH.rid
= a.aref_region

abstract let frameOf_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (frameOf_aref (aref_of r) == frameOf r)
  [SMTPat (frameOf_aref (aref_of r))]
= ()

abstract let aref_as_addr
  (a: aref)
: GTot nat
= HH.addr_of_aref a.aref_aref

abstract let aref_as_addr_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (aref_as_addr (aref_of r) == as_addr r)
  [SMTPat (aref_as_addr (aref_of r))]
= HH.addr_of_aref_of r.ref

abstract let aref_is_mm
  (r: aref)
: GTot bool
= HH.aref_is_mm r.aref_aref

abstract let is_mm_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (aref_is_mm (aref_of r) == is_mm r)
  [SMTPat (aref_is_mm (aref_of r))]
= HH.is_mm_aref_of r.ref

abstract let aref_unused_in
  (a: aref)
  (h: mem)
: GTot Type0
= ~ (live_region h a.aref_region) \/
  HH.aref_unused_in a.aref_aref h.h

abstract let unused_in_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
  (h: mem)
: Lemma
  (aref_unused_in (aref_of r) h <==> unused_in r h)
  [SMTPat (aref_unused_in (aref_of r) h)]
= HH.unused_in_aref_of r.ref h.h

abstract
val contains_aref_unused_in: #a:Type -> #rel: preorder a -> h:mem -> x:mreference a rel -> y:aref -> Lemma
  (requires (contains h x /\ aref_unused_in y h))
  (ensures  (frameOf x <> frameOf_aref y \/ as_addr x <> aref_as_addr y))
  [SMTPat (contains h x); SMTPat (aref_unused_in y h)]
let contains_aref_unused_in #a #rel h x y =
  if frameOf x = frameOf_aref y
  then HH.contains_ref_aref_unused_in h.h x.ref y.aref_aref
  else ()

(* Elimination rule *)

abstract
let aref_live_at
  (h: mem)
  (a: aref)
  (v: Type)
  (rel: preorder v)
: GTot Type0
= live_region h a.aref_region
  /\ HH.aref_live_at h.h a.aref_aref v rel

abstract
let greference_of
  (a: aref)
  (v: Type)
  (rel: preorder v)
: Ghost (mreference v rel)
  (requires (exists h . aref_live_at h a v rel))
  (ensures (fun _ -> True))
= MkRef a.aref_region (HH.grref_of a.aref_aref v rel)

abstract
let reference_of
  (h: mem)
  (a: aref)
  (v: Type)
  (rel: preorder v)
: Pure (mreference v rel)
  (requires (aref_live_at h a v rel))
  (ensures (fun x -> aref_live_at h a v rel /\ frameOf x == frameOf_aref a /\ as_addr x == aref_as_addr a /\ is_mm x == aref_is_mm a))
= MkRef a.aref_region (HH.rref_of h.h a.aref_aref v rel)

abstract
let aref_live_at_aref_of
  (h: mem)
  (#t: Type0)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (aref_live_at h (aref_of r) t rel <==> contains h r)
  [SMTPat (aref_live_at h (aref_of r) t rel)]
= ()

abstract
let contains_greference_of
  (h: mem)
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h' . aref_live_at h' a t rel))
  (ensures ((exists h' . aref_live_at h' a t rel) /\ (contains h (greference_of a t rel) <==> aref_live_at h a t rel)))
  [SMTPatOr [
    [SMTPat (contains h (greference_of a t rel))];
    [SMTPat (aref_live_at h a t rel)];
  ]]
= ()

abstract
let aref_of_greference_of
  (a: aref)
  (v: Type0)
  (rel: preorder v)
: Lemma
  (requires (exists h' . aref_live_at h' a v rel))
  (ensures ((exists h' . aref_live_at h' a v rel) /\ aref_of (greference_of a v rel) == a))
  [SMTPat (aref_of (greference_of a v rel))]
= ()

(* Operators lowered to rref *)

abstract let frameOf_greference_of
  (a: aref)
  (t: Type)
  (rel: preorder t)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ frameOf (greference_of a t rel) == frameOf_aref a))
  [SMTPat (frameOf (greference_of a t rel))]
= ()

abstract
let as_addr_greference_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ as_addr (greference_of a t rel) == aref_as_addr a))
  [SMTPat (as_addr (greference_of a t rel))]
= assert (addr_of (grref_of a.aref_aref t rel) == addr_of_aref a.aref_aref)

abstract
let is_mm_greference_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ is_mm (greference_of a t rel) == aref_is_mm a))
  [SMTPat (is_mm (greference_of a t rel))]
= ()  

abstract
let unused_in_greference_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
  (h: mem)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ (unused_in (greference_of a t rel) h <==> aref_unused_in a h)))
  [SMTPat (unused_in (greference_of a t rel) h)]
= ()

abstract
let sel_reference_of
  (a: aref)
  (v: Type0)
  (rel: preorder v)
  (h1 h2: mem)
: Lemma
  (requires (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel))
  (ensures (aref_live_at h2 a v rel /\ sel h1 (reference_of h2 a v rel) == sel h1 (greference_of a v rel)))
  [SMTPat (sel h1 (reference_of h2 a v rel))]
= ()

abstract
let upd_reference_of
  (a: aref)
  (v: Type0)
  (rel: preorder v)
  (h1 h2: mem)
  (x: v)
: Lemma
  (requires (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel))
  (ensures (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel /\ upd h1 (reference_of h2 a v rel) x == upd h1 (greference_of a v rel) x))
  [SMTPat (upd h1 (reference_of h2 a v rel) x)]
= ()
