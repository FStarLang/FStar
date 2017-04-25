module FStar.HyperStack
open FStar.Monotonic.HyperHeap

open FStar.Preorder

module M   = FStar.Map
module MH  = FStar.Monotonic.Heap
module MHH = FStar.Monotonic.HyperHeap

let is_in (r:rid) (h:MHH.t) = h `Map.contains` r

let is_stack_region r = color r > 0
let is_eternal_color c = c <= 0
let is_eternal_region r  = is_eternal_color (color r)

type sid = r:rid{is_stack_region r} //stack region ids

let is_above r1 r2      = r1 `includes` r2
let is_just_below r1 r2 = r1 `extends`  r2
let is_below r1 r2      = r2 `is_above` r1
let is_strictly_below r1 r2 = r1 `is_below` r2 && r1<>r2
let is_strictly_above r1 r2 = r1 `is_above` r2 && r1<>r2

let downward_closed (h:MHH.t) = 
  forall (r:rid). r `is_in` h  //for any region in the memory
        ==> (r=MHH.root    //either is the root
	    \/ (forall (s:rid). r `is_above` s  //or, any region beneath it
			  /\ s `is_in` h   //that is also in the memory
		     ==> (is_stack_region r = is_stack_region s))) //must be of the same flavor as itself

let is_tip (tip:MHH.rid) (h:MHH.t) = 
  (is_stack_region tip \/ tip=MHH.root)                                  //the tip is a stack region, or the root
  /\ tip `is_in` h                                                      //the tip is active
  /\ (forall (r:sid). r `is_in` h <==> r `is_above` tip)                      //any other sid activation is a above (or equal to) the tip

let hh = h:MHH.t{MHH.root `is_in` h /\ MHH.map_invariant h /\ downward_closed h}        //the memory itself, always contains the root region, and the parent of any active region is active

noeq type mem =
  | HS : h:hh
      -> tip:rid{tip `is_tip` h}                                                   //the id of the current top-most region
      -> mem

let empty_mem (m:MHH.t) = 
  let empty_map = Map.restrict (Set.empty) m in 
  let h = Map.upd empty_map MHH.root MH.emp in 
  let tip = MHH.root in 
  HS h tip

let test0 (m:mem) (r:rid{r `is_above` m.tip}) = 
    assert (r `is_in` m.h)

let test1 (m:mem) (r:rid{r `is_above` m.tip}) = 
    assert (r=MHH.root \/ is_stack_region r)

let test2 (m:mem) (r:sid{m.tip `is_above` r /\ m.tip <> r}) =  
   assert (~ (r `is_in` m.h))

let dc_elim (h:MHH.t{downward_closed h}) (r:rid{r `is_in` h /\ r <> MHH.root}) (s:rid)
  : Lemma (r `is_above` s /\ s `is_in` h ==> is_stack_region r = is_stack_region s)
  = ()	  

let test3 (m:mem) (r:rid{r <> MHH.root /\ is_eternal_region r /\ m.tip `is_above` r /\ is_stack_region m.tip})
  : Lemma (~ (r `is_in` m.h))
  = root_has_color_zero()

let test4 (m:mem) (r:rid{r <> MHH.root /\ is_eternal_region r /\ r `is_above` m.tip /\ is_stack_region m.tip})
  : Lemma (~ (r `is_in` m.h))
  = ()

let eternal_region_does_not_overlap_with_tip (m:mem) (r:rid{is_eternal_region r /\ not (MHH.disjoint r m.tip) /\ r<>MHH.root /\ is_stack_region m.tip})
  : Lemma (requires True)
	  (ensures (~ (r `is_in` m.h)))
  = root_has_color_zero()

let poppable m = m.tip <> MHH.root

let remove_elt (#a:eqtype) (s:Set.set a) (x:a) = Set.intersect s (Set.complement (Set.singleton x))

let popped m0 m1 =
  poppable m0
  /\ MHH.parent m0.tip = m1.tip
  /\ Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip)
  /\ Map.equal m1.h (Map.restrict (Map.domain m1.h) m0.h)

let pop (m0:mem{poppable m0}) : GTot mem =
  root_has_color_zero();
  let dom = remove_elt (Map.domain m0.h) m0.tip in
  let h0 = m0.h in
  let h1 = Map.restrict dom m0.h in
  let tip0 = m0.tip in
  let tip1 = MHH.parent tip0 in
  assert (forall (r:sid). Map.contains h1 r ==>
  	    (forall (s:sid). includes s r ==> Map.contains h1 s));
  HS h1 tip1

//A (reference a) may reside in the stack or heap, and may be manually managed
noeq type reference (a:Type) (rel:preorder a) =
  | MkRef : id:rid -> ref:MHH.mrref id a rel -> reference a rel

let is_mm (#a:Type) (#rel:preorder a) (r:reference a rel) :GTot bool = MHH.is_mm r.ref

//adding (not s.mm) to stackref and ref so as to keep their semantics as is
let stackref (a:Type) (rel:preorder a) = s:reference a rel { is_stack_region s.id && not (is_mm s) }
let ref (a:Type) (rel:preorder a) = s:reference a rel{is_eternal_region s.id && not (is_mm s)}

let mmstackref (a:Type) (rel:preorder a) = s:reference a rel{is_stack_region s.id && is_mm s }
let mmref (a:Type) (rel:preorder a) = s:reference a rel{is_eternal_region s.id && is_mm s}

(*
 * The Map.contains conjunct is necessary to prove that upd
 * returns a valid mem. In particular, without Map.contains,
 * we cannot prove the eternal regions invariant that all
 * included regions of a region are also in the map.
 *)
let live_region (m:mem) (i:rid) =
  (is_eternal_region i \/ i `is_above` m.tip)
  /\ Map.contains m.h i

let weak_live_region (m:mem) (i:rid) =
  is_eternal_region i \/ i `is_above` m.tip

let contains (#a:Type) (#rel:preorder a) (m:mem) (s:reference a rel) =
  live_region m s.id
  /\ MHH.contains_ref s.ref m.h

let unused_in (#a:Type) (#rel:preorder a) (r:reference a rel) (h:mem) =
  ~ (live_region h r.id) \/
  MHH.unused_in r.ref h.h

private val weak_live_region_implies_eternal_or_in_map: r:rid -> m:mem -> Lemma
  (requires (weak_live_region m r))
  (ensures (is_eternal_region r \/ Map.contains m.h r))
let weak_live_region_implies_eternal_or_in_map r m = ()

let weak_contains (#a:Type) (#rel:preorder a) (m:mem) (s:reference a rel) =
  weak_live_region m s.id /\
  (if is_mm s then MHH.weak_contains_ref s.ref m.h else True)

let upd_condition (#a:Type) (#rel:preorder a) (m:mem) (s:reference a rel) (x:a) 
  = rel (sel (m.h) s.ref) x

let upd (#a:Type) (#rel:preorder a) (m:mem) (s:reference a rel{live_region m s.id}) (v:a{upd_condition m s v})
  : GTot mem
  = HS (m.h.[s.ref] <- v) m.tip

let sel (#a:Type) (#rel:preorder a) (m:mem) (s:reference a rel)
  : GTot a
  = m.h.[s.ref]

let equal_domains (m0:mem) (m1:mem) =
  m0.tip = m1.tip
  /\ Set.equal (Map.domain m0.h) (Map.domain m1.h)
  /\ (forall r. Map.contains m0.h r ==> MH.equal_dom (Map.sel m0.h r) (Map.sel m1.h r))

let lemma_equal_domains_trans (m0:mem) (m1:mem) (m2:mem) : Lemma
  (requires (equal_domains m0 m1 /\ equal_domains m1 m2))
  (ensures  (equal_domains m0 m2))
  [SMTPat (equal_domains m0 m1); SMTPat (equal_domains m1 m2)]
  = ()

let equal_stack_domains (m0:mem) (m1:mem) =
  m0.tip = m1.tip
  /\ (forall r. (is_stack_region r /\ r `is_above` m0.tip) ==> MH.equal_dom (Map.sel m0.h r) (Map.sel m1.h r))

let lemma_equal_stack_domains_trans (m0:mem) (m1:mem) (m2:mem) : Lemma
  (requires (equal_stack_domains m0 m1 /\ equal_stack_domains m1 m2))
  (ensures  (equal_stack_domains m0 m2))
  [SMTPat (equal_stack_domains m0 m1); SMTPat (equal_stack_domains m1 m2)]
  = ()

let modifies (s:Set.set rid) (m0:mem) (m1:mem) =
  MHH.modifies_just s m0.h m1.h
  /\ m0.tip=m1.tip

let modifies_transitively (s:Set.set rid) (m0:mem) (m1:mem) =
  MHH.modifies s m0.h m1.h
  /\ m0.tip=m1.tip

let heap_only (m0:mem) =
  m0.tip = MHH.root

let top_frame (m:mem) = Map.sel m.h m.tip
  
let fresh_frame (m0:mem) (m1:mem) =
  not (Map.contains m0.h m1.tip)
  /\ MHH.parent m1.tip = m0.tip
  /\ m1.h == Map.upd m0.h m1.tip MH.emp

let modifies_drop_tip (m0:mem) (m1:mem) (m2:mem) (s:Set.set rid)
    : Lemma (fresh_frame m0 m1 /\
	     modifies_transitively (Set.union s (Set.singleton m1.tip)) m1 m2 ==> 
	     modifies_transitively s m0 (pop m2))
    = ()

let lemma_pop_is_popped (m0:mem{poppable m0})
  : Lemma (popped m0 (pop m0))
  = let m1 = pop m0 in
    assert (Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip))

type s_ref (i:rid) (a:Type) (rel:preorder a) = s:reference a rel{s.id = i}

let frameOf #a #rel (s:reference a rel) = s.id

let as_mref #a #rel (x:reference a rel)  : GTot (MH.mref a rel) = MHH.as_mref #a #rel #x.id x.ref
let as_addr #a #rel (x:reference a rel) : GTot nat = MH.addr_of (MHH.as_mref #a #rel #x.id x.ref)
let modifies_one id h0 h1 = MHH.modifies_one id h0.h h1.h
let modifies_ref (id:rid) (s:Set.set nat) (h0:mem) (h1:mem) =
  MHH.modifies_rref id s h0.h h1.h /\ h1.tip=h0.tip

let lemma_upd_1 #a #rel (h:mem) (x:reference a rel) (v:a{upd_condition h x v}) : Lemma
  (requires (contains h x))
  (ensures (contains h x
	    /\ modifies_one (frameOf x) h (upd h x v)
	    /\ modifies_ref (frameOf x) (Set.singleton (as_addr x)) h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPatT (contains h x)]
  = ()

let lemma_upd_2 (#a:Type) (#rel:preorder a) (h:mem) (x:reference a rel) (v:a{upd_condition h x v}) : Lemma
  (requires (frameOf x = h.tip /\ x `unused_in` h))
  (ensures (frameOf x = h.tip
	    /\ modifies_one h.tip h (upd h x v)
	    /\ modifies_ref h.tip Set.empty h (upd h x v)
	    /\ sel (upd h x v) x == v ))
  [SMTPat (upd h x v); SMTPatT (x `unused_in` h)]
  = ()

(*val lemma_live_1_aux: #a:Type ->  #a':Type -> #rel:preorder a -> #rel':preorder a' -> h:mem -> x:reference a rel -> x':reference a' rel' -> Lemma
  //(requires (contains h x /\ MH.unused_in #a' #rel' (MHH.as_mref x'.ref) (Map.sel h.h x'.id)))
  (requires (Map.contains h.h x.id /\ MH.contains (Map.sel h.h x.id) (MHH.as_mref x.ref) /\ MH.unused_in #a' #rel' (MHH.as_mref x'.ref) (Map.sel h.h x'.id)))
  (ensures  (x.id <> x'.id \/ ~ (as_mref x === as_mref x')))
  [SMTPat (contains h x); SMTPat (x' `unused_in` h)]
let lemma_live_1_aux #a #a' #rel #rel' h x x' = ()*)

val lemma_live_1: #a:Type ->  #a':Type -> #rel:preorder a -> #rel':preorder a' -> h:mem -> x:reference a rel -> x':reference a' rel' -> Lemma
  (requires (contains h x /\ x' `unused_in` h))
  (ensures  (x.id <> x'.id \/ ~ (as_mref x === as_mref x')))
  [SMTPat (contains h x); SMTPat (x' `unused_in` h)]
let lemma_live_1 #a #a' #rel #rel' h x x' = admit () //TODO: need to remove this admit, this lemma holds trivially for non-monotonic HyperStack

let above_tip_is_live (#a:Type) (#rel:preorder a) (m:mem) (x:reference a rel) : Lemma
  (requires (x.id `is_above` m.tip))
  (ensures (x.id `is_in` m.h))
  = ()

(*
 * AR: relating contains and weak_contains.
 *)
let contains_implies_weak_contains (#a:Type) (#rel:preorder a) (h:mem) (x:reference a rel) :Lemma
  (requires (True))
  (ensures (contains h x ==> weak_contains h x))
  [SMTPatOr [[SMTPat (contains h x)]; [SMTPat (weak_contains h x)]] ]
  = ()

noeq type some_mref =
| Ref : #a:Type0 -> #rel:preorder a -> reference a rel -> some_mref

let some_mrefs = list some_mref

let rec regions_of_some_mrefs (rs:some_mrefs) : Tot (Set.set rid) = 
  match rs with
  | [] -> Set.empty
  | (Ref r)::tl -> Set.union (Set.singleton r.id) (regions_of_some_mrefs tl)

let rec mrefs_in_region (r:rid) (rs:some_mrefs) : GTot (Set.set nat) =
  match rs with
  | []         -> Set.empty
  | (Ref x)::tl ->
    Set.union (if x.id=r then Set.singleton (as_addr x) else Set.empty)
               (mrefs_in_region r tl)

unfold let mods (rs:some_mrefs) h0 h1 =
    modifies (normalize_term (regions_of_some_mrefs rs)) h0 h1
  /\ (forall (r:rid). modifies_ref r (normalize_term (mrefs_in_region r rs)) h0 h1)

////////////////////////////////////////////////////////////////////////////////
let eternal_disjoint_from_tip (h:mem{is_stack_region h.tip})
			      (r:rid{is_eternal_region r /\
				     r<>MHH.root /\
				     r `is_in` h.h})
   : Lemma (MHH.disjoint h.tip r)
   = ()
   
////////////////////////////////////////////////////////////////////////////////
(*#set-options "--initial_fuel 0 --max_fuel 0 --log_queries"
let f (a:Type0) (b:Type0) (rela:preorder a) (relb:preorder b) 
                          (x:reference a rela) (x':reference a rela) 
			  (y:reference b relb) (z:reference nat) 
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
  ()*)


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

