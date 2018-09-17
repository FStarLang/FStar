module FStar.HyperStack.ST

open FStar.HyperStack

module W  = FStar.Monotonic.Witnessed
module HS = FStar.HyperStack

open FStar.Preorder

(* Setting up the preorder for mem *)

(* Starting the predicates that constitute the preorder *)

[@"opaque_to_smt"]
private unfold let contains_region (m:mem) (r:rid) = get_hmap m `Map.contains` r

(* Eternal regions remain contained *)
private abstract let eternal_region_pred (m1 m2:mem) :Type0
  = forall (r:HS.rid).{:pattern (HS.is_eternal_color (color r)); (m1 `contains_region` r)}
                 (HS.is_eternal_color (color r) /\ m1 `contains_region` r) ==> m2 `contains_region` r

(* rid counter increases monotonically *)
private abstract let rid_ctr_pred (m1 m2:mem) :Type0 = get_rid_ctr m1 <= get_rid_ctr m2

(*
 * A region r, that is:
 * (a) not contained in m1, and
 * (b) has rid last component less than m1.rid_ctr
 * 
 * remains not contained in m2
 *)
private abstract let rid_last_component_pred (m1 m2:mem) :Type0
  = forall (r:HS.rid).{:pattern (m1 `contains_region` r)}
                 ((~ (m1 `contains_region` r)) /\ rid_last_component r < get_rid_ctr m1) ==>
		 (~ (m2 `contains_region` r))

(* Predicate for eternal refs *)
private abstract let eternal_refs_pred (m1 m2:mem) :Type0
  = forall (a:Type) (rel:preorder a) (r:HS.mreference a rel).
      {:pattern (m1 `HS.contains` r)}
      if is_mm r then True
      else
        if m1 `HS.contains` r then
	  if HS.is_eternal_color (color (HS.frameOf r)) then m2 `HS.contains` r /\ rel (HS.sel m1 r) (HS.sel m2 r)
	  else if m2 `contains_region` (HS.frameOf r) then m2 `HS.contains` r /\ rel (HS.sel m1 r) (HS.sel m2 r)
	  else True
	else True

(*
 * Predicate for next ref address in a region's heap
 * For all regions, their next_addr increases monotonically (or the region ceases to exist)
 *)
private abstract let next_ref_addr_in_a_region_pred (m1 m2:mem) :Type0
  = forall (r:HS.rid).{:pattern (m1 `contains_region` r)}
                 (m1 `contains_region` r) ==> 
		 (if m2 `contains_region` r then
		    let h1 = Map.sel (HS.get_hmap m1) r in
		    let h2 = Map.sel (HS.get_hmap m2) r in
		    Heap.next_addr h1 <= Heap.next_addr h2
		  else True)

(* Predicate that an unused ref whose addr is less than the next addr remains unused *)
private abstract let unused_ref_next_addr_pred (m1 m2:mem) :Type0
  = forall (rid:HS.rid).{:pattern (m1 `contains_region` rid)}
                   (m1 `contains_region` rid) ==>
		   (let h1 = Map.sel (HS.get_hmap m1) rid in
		    (forall (a:Type0) (rel:preorder a) (r:HS.mreference a rel).{:pattern (r `HS.unused_in` m1)}
		       (HS.frameOf r == rid /\ r `HS.unused_in` m1 /\ HS.as_addr r < Heap.next_addr h1) ==>
		       (r `HS.unused_in` m2)))

(* Predicate for mm refs *)
private abstract let mm_refs_pred (m1 m2:mem) :Type0
  = forall (a:Type) (rel:preorder a) (r:HS.mreference a rel).{:pattern (m1 `HS.contains` r)}
      if not (is_mm r) then True
      else
        if m1 `HS.contains` r then
	  (m2 `HS.contains` r /\ rel (HS.sel m1 r) (HS.sel m2 r)) \/
	  (r `HS.unused_in` m2)
	else True

(* The preorder is the conjunction of above predicates *)
private abstract let mem_rel :relation mem
  = fun (m1 m2:mem) ->
    eternal_region_pred m1 m2 /\ rid_ctr_pred m1 m2 /\ rid_last_component_pred m1 m2 /\ eternal_refs_pred m1 m2 /\
    next_ref_addr_in_a_region_pred m1 m2 /\ unused_ref_next_addr_pred m1 m2 /\ mm_refs_pred m1 m2

private abstract let mem_pre :preorder mem =
  HS.lemma_rid_ctr_pred (); HS.lemma_next_addr_contained_refs_addr ();
  mem_rel

type mem_predicate = mem -> Type0

(* Predicates that we will witness with regions and refs *)
abstract let region_contains_pred (r:HS.rid) :mem_predicate
  = fun m -> (not (HS.is_eternal_color (color r))) \/ m `contains_region` r

abstract let ref_contains_pred (#a:Type) (#rel:preorder a) (r:HS.mreference a rel) :mem_predicate
  = fun m ->
    let rid = HS.frameOf r in
    rid_last_component rid < get_rid_ctr m /\
    (m `contains_region` rid ==> (
     (HS.as_addr r < Heap.next_addr (Map.sel (HS.get_hmap m) rid)) /\
     (HS.is_mm r ==> (m `HS.contains` r \/ r `HS.unused_in` m)) /\
     ((not (HS.is_mm r)) ==> m `HS.contains` r)))

(***** Global ST (GST) effect with put, get, witness, and recall *****)

new_effect GST = STATE_h mem

let gst_pre           = st_pre_h mem
let gst_post' (a:Type) (pre:Type) = st_post_h' mem a pre
let gst_post (a:Type) = st_post_h mem a
let gst_wp (a:Type)   = st_wp_h mem a

unfold let lift_div_gst (a:Type) (wp:pure_wp a) (p:gst_post a) (h:mem) = wp (fun a -> p a h)
sub_effect DIV ~> GST = lift_div_gst

(*
 * AR: A few notes about the interface:
 *     - The interface closely mimics the interface we formalized in our POPL'18 paper
 *     - Specifically, `witnessed` is defined for any mem_predicate (not necessarily stable ones)
 *     - `stable p` is a precondition for `gst_witness`
 *     - `gst_recall` does not have a precondition for `stable p`, since `gst_witness` is the only way
 *       clients would have obtained `witnessed p`, and so, `p` should already be stable
 *     - `lemma_functoriality` does not require stablility for either `p` or `q`
 *       Our metatheory ensures that this is sound (without requiring stability of `q`)
 *       This form is useful in defining the MRRef interface (see mr_witness)
 *)
       
abstract let stable (p:mem_predicate) :Type0 =
  forall (h1:mem) (h2:mem).{:pattern (mem_rel h1 h2)} (p h1 /\ mem_rel h1 h2) ==> p h2

abstract let witnessed (p:mem_predicate) :Type0 = W.witnessed mem_rel p

(* TODO: we should derive these using DM4F *)
assume private val gst_get: unit    -> GST mem (fun p h0 -> p h0 h0)
assume private val gst_put: h1:mem -> GST unit (fun p h0 -> mem_rel h0 h1 /\ p () h1)

assume private val gst_witness: p:mem_predicate -> GST unit (fun post h0 -> p h0 /\ stable p /\ (witnessed p ==> post () h0))
assume private val gst_recall:  p:mem_predicate -> GST unit (fun post h0 -> witnessed p /\ (p h0 ==> post () h0))

val lemma_functoriality (p:mem_predicate{witnessed p}) (q:mem_predicate{(forall (h:mem). p h ==> q h)})
  : Lemma (ensures (witnessed q))
let lemma_functoriality p q = W.lemma_witnessed_weakening mem_rel p q

let st_pre   = gst_pre
let st_post' = gst_post'
let st_post  = gst_post
let st_wp    = gst_wp

new_effect STATE = GST

unfold let lift_gst_state (a:Type) (wp:gst_wp a) = wp
sub_effect GST ~> STATE = lift_gst_state

(* effect State (a:Type) (wp:st_wp a) = *)
(*        STATE a wp *)

(**
    WARNING: this effect is unsafe, for C/C++ extraction it shall only be used by
    code that would later extract to OCaml or by library functions
    *)
effect Unsafe (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. pre h /\ post h a h1 ==> p a h1)) (* WP *)

(****** defining predicates for equal refs in some regions ******)

(*
//  * AR: (may be this is an overkill)
//  *     various effects below talk about refs being equal in some regions (all regions, stack regions, etc.)
//  *     this was done by defining, for example, an equal_dom predicate with a (forall (r:rid)) quantifier
//  *     this quantifier was only guarded with Map.contains (HS.get_hmap m) r
//  *     which meant it could fire for all the contained regions
//  *
//  *     instead now we define abstract predicates, e.g. same_refs_in_all_regions, and provide intro and elim forms
//  *     the advantage is that, the (lemma) quantifiers are now guarded additionally by same_refs_in_all_regions kind
//  *       of predicates, and hence should fire more contextually
//  *     should profile the queries to see if it actually helps
//  *)

(*
//  * marking these opaque, since expect them to be unfolded away beforehand
//  *)
[@"opaque_to_smt"]
unfold private let equal_heap_dom (r:rid) (m0 m1:mem) :Type0
  = Heap.equal_dom (get_hmap m0 `Map.sel` r) (get_hmap m1 `Map.sel` r)

[@"opaque_to_smt"]
unfold private let contained_region :mem -> mem -> rid -> Type0
  = fun m0 m1 r -> m0 `contains_region` r /\ m1 `contains_region` r

[@"opaque_to_smt"]
unfold private let contained_stack_region :mem -> mem -> rid -> Type0
  = fun m0 m1 r -> is_stack_region r /\ contained_region m0 m1 r

[@"opaque_to_smt"]
unfold private let contained_non_tip_region :mem -> mem -> rid -> Type0
  = fun m0 m1 r -> r =!= get_tip m0 /\ r =!= get_tip m1 /\ contained_region m0 m1 r

[@"opaque_to_smt"]
unfold private let contained_non_tip_stack_region :mem -> mem -> rid -> Type0
  = fun m0 m1 r -> is_stack_region r /\ contained_non_tip_region m0 m1 r

[@"opaque_to_smt"]
unfold private let same_refs_common (p:mem -> mem -> rid -> Type0) (m0 m1:mem) =
  forall (r:rid). p m0 m1 r ==> equal_heap_dom r m0 m1

(* predicates *)
abstract let same_refs_in_all_regions (m0 m1:mem) :Type0
  = same_refs_common contained_region m0 m1
abstract let same_refs_in_stack_regions (m0 m1:mem) :Type0
  = same_refs_common contained_stack_region m0 m1
abstract let same_refs_in_non_tip_regions (m0 m1:mem) :Type0
  = same_refs_common contained_non_tip_region m0 m1
abstract let same_refs_in_non_tip_stack_regions (m0 m1:mem) :Type0
  = same_refs_common contained_non_tip_stack_region m0 m1

(* intro and elim forms *)
let lemma_same_refs_in_all_regions_intro (m0 m1:mem)
  :Lemma (requires (same_refs_common contained_region m0 m1)) (ensures  (same_refs_in_all_regions m0 m1))
	 [SMTPat (same_refs_in_all_regions m0 m1)] = ()
let lemma_same_refs_in_all_regions_elim (m0 m1:mem) (r:rid)
  :Lemma (requires (same_refs_in_all_regions m0 m1 /\ contained_region m0 m1 r)) (ensures  (equal_heap_dom r m0 m1))
	 [SMTPatOr [[SMTPat (same_refs_in_all_regions m0 m1); SMTPat (m0 `contains_region` r)];
                    [SMTPat (same_refs_in_all_regions m0 m1); SMTPat (m1 `contains_region` r)]]] = ()
let lemma_same_refs_in_stack_regions_intro (m0 m1:mem)
  :Lemma (requires (same_refs_common contained_stack_region m0 m1)) (ensures  (same_refs_in_stack_regions m0 m1))
	 [SMTPat  (same_refs_in_stack_regions m0 m1)] = ()
let lemma_same_refs_in_stack_regions_elim (m0 m1:mem) (r:rid)
  :Lemma (requires (same_refs_in_stack_regions m0 m1 /\ contained_stack_region m0 m1 r)) (ensures  (equal_heap_dom r m0 m1))
	 [SMTPatOr [[SMTPat (same_refs_in_stack_regions m0 m1); SMTPat (is_stack_region r); SMTPat (m0 `contains_region` r)];
                    [SMTPat (same_refs_in_stack_regions m0 m1); SMTPat (is_stack_region r); SMTPat (m1 `contains_region` r)]]]
  = ()

let lemma_same_refs_in_non_tip_regions_intro (m0 m1:mem)
  :Lemma (requires (same_refs_common contained_non_tip_region m0 m1)) (ensures (same_refs_in_non_tip_regions m0 m1))
         [SMTPat (same_refs_in_non_tip_regions m0 m1)] = ()
let lemma_same_refs_in_non_tip_regions_elim (m0 m1:mem) (r:rid)
  :Lemma (requires (same_refs_in_non_tip_regions m0 m1 /\ contained_non_tip_region m0 m1 r)) (ensures  (equal_heap_dom r m0 m1))
	 [SMTPatOr [[SMTPat (same_refs_in_non_tip_regions m0 m1); SMTPat (m0 `contains_region` r)];
                    [SMTPat (same_refs_in_non_tip_regions m0 m1); SMTPat (m1 `contains_region` r)]]]
  = ()	 

let lemma_same_refs_in_non_tip_stack_regions_intro (m0 m1:mem)
  :Lemma (requires (same_refs_common contained_non_tip_stack_region m0 m1)) (ensures (same_refs_in_non_tip_stack_regions m0 m1))
         [SMTPat (same_refs_in_non_tip_stack_regions m0 m1)] = ()
let lemma_same_refs_in_non_tip_stack_regions_elim (m0 m1:mem) (r:rid)
  :Lemma (requires (same_refs_in_non_tip_stack_regions m0 m1 /\ contained_non_tip_stack_region m0 m1 r))
         (ensures  (equal_heap_dom r m0 m1))
	 [SMTPatOr [[SMTPat (same_refs_in_non_tip_stack_regions m0 m1); SMTPat (is_stack_region r); SMTPat (m0 `contains_region` r);];
                    [SMTPat (same_refs_in_non_tip_stack_regions m0 m1); SMTPat (is_stack_region r); SMTPat (m1 `contains_region` r)]]]
  = ()	 

(******)

let equal_domains (m0 m1:mem) =
  get_tip m0 == get_tip m1 /\
  Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)) /\
  same_refs_in_all_regions m0 m1

let lemma_equal_domains_trans (m0 m1 m2:mem)
  :Lemma (requires (equal_domains m0 m1 /\ equal_domains m1 m2))
         (ensures  (equal_domains m0 m2))
         [SMTPat (equal_domains m0 m1); SMTPat (equal_domains m1 m2)]
  = ()

(**
 * Effect of stacked based code: the 'equal_domains' clause enforces that
 * - both mem have the same tip
 * - both mem reference the same heaps (their map: rid -> heap have the same domain)
 * - in each region id, the corresponding heaps contain the same references on both sides
 *)
effect Stack (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ equal_domains h h1) ==> p a h1)) (* WP *)

(**
 * Effect of heap-based code.
 * - assumes that the stack is empty (tip = root)
 * - corresponds to the HyperHeap ST effect
 * - can call to Stack and ST code freely
 * - respects the stack invariant: the stack has to be empty when returning
 *)
effect Heap (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ get_tip h = HS.root /\ get_tip h1 = HS.root ) ==> p a h1)) (* WP *)

let equal_stack_domains (m0 m1:mem) =
  get_tip m0 == get_tip m1 /\
  same_refs_in_stack_regions m0 m1

(**
 * Effect of low-level code:
 * - maintains the allocation invariant on the stack: no allocation unless in a new frame that has to be popped before returning
 * - not constraints on heap allocation
 *)
effect ST (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ equal_stack_domains h h1) ==> p a h1)) (* WP *)

effect St (a:Type) = ST a (fun _ -> True) (fun _ _ _ -> True)

let inline_stack_inv h h' : GTot Type0 =
  (* The frame invariant is enforced *)
  get_tip h == get_tip h' /\
  (* The heap structure is unchanged *)
  Map.domain (get_hmap h) == Map.domain (get_hmap h') /\
  (* Any region that is not the tip has no seen any allocation *)
  same_refs_in_non_tip_regions h h'

(**
 * Effect that indicates to the Kremlin compiler that allocation may occur in the caller's frame.
 * In other terms, the backend has to unfold the body into the caller's body.
 * This effect maintains the stack AND the heap invariant: it can be inlined in the Stack effect
 * function body as well as in a Heap effect function body
 *)
effect StackInline (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ is_stack_region (get_tip h) /\ (forall a h1. (pre h /\ post h a h1 /\ inline_stack_inv h h1) ==> p a h1)) (* WP *)

let inline_inv h h' : GTot Type0 =
  (* The stack invariant is enforced *)
  get_tip h == get_tip h' /\
  (* No frame may have received an allocation but the tip *)
  same_refs_in_non_tip_stack_regions h h'

(**
 * Effect that indicates to the Kremlin compiler that allocation may occur in the caller's frame.
 * In other terms, the backend has to unfold the body into the caller's body.
 * This effect only maintains the stack invariant: the tip is left unchanged and no allocation
 *  may occurs in the stack lower than the tip.
 * Region allocation is not constrained.
 * Heap allocation is not constrained.
 *)
effect Inline (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ inline_inv h h1) ==> p a h1)) (* WP *)

(**
 * TODO:
 * REMOVE AS SOON AS CONSENSUS IS REACHED ON NEW LOW EFFECT NAMES
 *)
effect STL (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) = Stack a pre post

sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:mem) -> wp (fun a -> p a h)


(*
 * AR: The clients should open HyperStack.ST after the memory model files (as with Heap and FStar.ST)
 *)

type mreference (a:Type) (rel:preorder a) =
  r:HS.mreference a rel{witnessed (ref_contains_pred r) /\
                        witnessed (region_contains_pred (HS.frameOf r))}
type mstackref (a:Type) (rel:preorder a) =
  r:HS.mstackref a rel{witnessed (ref_contains_pred r) /\
                       witnessed (region_contains_pred (HS.frameOf r))}
type mref (a:Type) (rel:preorder a) =
  r:HS.mref a rel{witnessed (ref_contains_pred r) /\
                  witnessed (region_contains_pred (HS.frameOf r))}
type mmmstackref (a:Type) (rel:preorder a) =
  r:HS.mmmstackref a rel{witnessed (ref_contains_pred r) /\
                         witnessed (region_contains_pred (HS.frameOf r))}
type mmmref (a:Type) (rel:preorder a) =
  r:HS.mmmref a rel{witnessed (ref_contains_pred r) /\
                    witnessed (region_contains_pred (HS.frameOf r))}
type s_mref (i:rid) (a:Type) (rel:preorder a) =
  r:HS.s_mref i a rel{witnessed (ref_contains_pred r) /\
                      witnessed (region_contains_pred (HS.frameOf r))}
type reference (a:Type) = mreference a (Heap.trivial_preorder a)
type stackref (a:Type) = mstackref a (Heap.trivial_preorder a)
type ref (a:Type) = mref a (Heap.trivial_preorder a)
type mmstackref (a:Type) = mmmstackref a (Heap.trivial_preorder a)
type mmref (a:Type) = mmmref a (Heap.trivial_preorder a)
type s_ref (i:rid) (a:Type) = s_mref i a (Heap.trivial_preorder a)

let is_eternal_region (r:rid) :Type0
  = HS.is_eternal_color (color r) /\ (r == HS.root \/ witnessed (region_contains_pred r))

(*
//  * AR: The change to using ST.rid may not be that bad itself,
//  *     since subtyping should take care of most instances in the client usage.
//  *     However, one case where it could be an issue is modifies clauses that use
//  *     Set.set rid.
//  *)

(**
//    Pushes a new empty frame on the stack
//    *)
let push_frame (_:unit) :Unsafe unit (requires (fun m -> True)) (ensures (fun (m0:mem) _ (m1:mem) -> fresh_frame m0 m1))
  = let m0 = gst_get () in
    let m1 = HS.hs_push_frame m0 in
    gst_put m1

(**
//    Removes old frame from the stack
//    *)
let pop_frame (_:unit)
  :Unsafe unit
  (requires (fun m -> poppable m))
  (ensures (fun (m0:mem) _ (m1:mem) -> poppable m0 /\ m1==pop m0 /\ popped m0 m1))
  = let m1 = pop (gst_get ()) in
    gst_put m1

let salloc_post (#a:Type) (#rel:preorder a) (init:a) (m0:mem)
                (s:mreference a rel{is_stack_region (frameOf s)}) (m1:mem)
  = is_stack_region (get_tip m0)                          /\
    Map.domain (get_hmap m0) == Map.domain (get_hmap m1)  /\
    get_tip m0 == get_tip m1                              /\
    frameOf s   = get_tip m1                              /\
    HS.fresh_ref s m0 m1                                  /\  //it's a fresh reference in the top frame
    m1 == HyperStack.upd m0 s init  //and it's been initialized

private let salloc_common (#a:Type) (#rel:preorder a) (init:a) (mm:bool)
  :StackInline (mreference a rel)
  (requires (fun m       -> is_stack_region (get_tip m)))
  (ensures  (fun m0 s m1 -> is_stack_region (HS.frameOf s) /\ salloc_post init m0 s m1 /\ is_mm s == mm))
  = let m0 = gst_get () in
    let r, m1 = HS.alloc rel (get_tip m0) init mm m0 in
    Heap.lemma_next_addr_alloc rel (Map.sel (get_hmap m0) (get_tip m0)) init mm;  //AR: to prove that next_addr in tip's heap increases (it is part of mem_rel)
    gst_put m1;
    assert (Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)));
    HS.lemma_rid_ctr_pred ();  //AR: to prove that rid_last_component of r.id is < rid_ctr
    gst_witness (ref_contains_pred r);
    gst_witness (region_contains_pred (HS.frameOf r));
    r

(**
 * Allocates on the top-most stack frame
 *)
let salloc (#a:Type) (#rel:preorder a) (init:a)
  :StackInline (mstackref a rel)
  (requires (fun m -> is_stack_region (get_tip m)))
  (ensures salloc_post init)
  = salloc_common init false
  
// JP, AR: these are not supported in C, and `salloc` already benefits from
// automatic memory management.
[@ (deprecated "use salloc instead") ]
let salloc_mm (#a:Type) (#rel:preorder a) (init:a)
  : StackInline (mmmstackref a rel)
  (requires (fun m -> is_stack_region (get_tip m)))
  (ensures salloc_post init)
  = salloc_common init true

[@ (deprecated "use salloc instead") ]
let sfree (#a:Type) (#rel:preorder a) (r:mmmstackref a rel)
  :StackInline unit
   (requires (fun m0 -> frameOf r = get_tip m0 /\ m0 `contains` r))
   (ensures (fun m0 _ m1 -> m0 `contains` r /\ m1 == HS.free r m0))
  = let m0 = gst_get () in
    let m1 = HS.free r m0 in
    assert (Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)));
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    Heap.lemma_next_addr_free_mm (Map.sel (HS.get_hmap m0) (HS.get_tip m0)) (HS.as_ref r);  //AR: to prove that next_addr in tip's heap remains same (to satisfy the predicate in mm rel)
    gst_put m1

let new_region (r0:rid)
  :ST rid
      (requires (fun m        -> is_eternal_region r0))
      (ensures  (fun m0 r1 m1 ->
                 r1 `HS.extends` r0                               /\
                 HS.fresh_region r1 m0 m1                         /\
		 HS.color r1 = HS.color r0                        /\
		 is_eternal_region r1                             /\
		 get_hmap m1 == Map.upd (get_hmap m0) r1 Heap.emp /\
		 get_tip m1 == get_tip m0 /\ 
                 HS.live_region m0 r0 /\
                 (r1, m1) == HS.new_eternal_region m0 r0 None
                 ))
  = if r0 <> HS.root then gst_recall (region_contains_pred r0);  //recall containment of r0
    HS.lemma_rid_ctr_pred ();
    let m0 = gst_get () in
    let new_rid, m1 = HS.new_eternal_region m0 r0 None in
    gst_put m1;
    gst_witness (region_contains_pred new_rid);
    new_rid

let is_eternal_color = HS.is_eternal_color

let new_colored_region (r0:rid) (c:int)
  :ST rid
      (requires (fun m       -> is_eternal_color c /\ is_eternal_region r0))
      (ensures (fun m0 r1 m1 ->
                r1 `HS.extends` r0                               /\
                HS.fresh_region r1 m0 m1                         /\
	        HS.color r1 = c                                  /\
		is_eternal_region r1                             /\
                HS.live_region m0 r0 /\
                (r1, m1) == HS.new_eternal_region m0 r0 (Some c) /\
	        get_hmap m1 == Map.upd (get_hmap m0) r1 Heap.emp /\
		get_tip m1 == get_tip m0))
  = if r0 <> HS.root then gst_recall (region_contains_pred r0);  //recall containment of r0
    HS.lemma_rid_ctr_pred ();
    let m0 = gst_get () in
    let new_rid, m1 = HS.new_eternal_region m0 r0 (Some c) in
    gst_put m1;
    gst_witness (region_contains_pred new_rid);
    new_rid

let ralloc_post (#a:Type) (#rel:preorder a) (i:rid) (init:a) (m0:mem)
                       (x:mreference a rel{is_eternal_region (frameOf x)}) (m1:mem) =
  let region_i = get_hmap m0 `Map.sel` i in
  as_ref x `Heap.unused_in` region_i /\
  i `is_in` get_hmap m0              /\
  i = frameOf x                      /\
  m1 == upd m0 x init                      

private let ralloc_common (#a:Type) (#rel:preorder a) (i:rid) (init:a) (mm:bool)
  :ST (mreference a rel)
      (requires (fun m       -> is_eternal_region i))
      (ensures  (fun m0 r m1 -> is_eternal_region (frameOf r) /\ ralloc_post i init m0 r m1 /\ is_mm r == mm))
  = if i <> HS.root then gst_recall (region_contains_pred i);
    let m0 = gst_get () in
    let r, m1 = HS.alloc rel i init mm m0 in
    Heap.lemma_next_addr_alloc rel (Map.sel (HS.get_hmap m0) i) init mm;  //AR: to prove that next_addr in tip's heap remains same (to satisfy the predicate in mm rel)
    gst_put m1;
    assert (Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)));
    HS.lemma_rid_ctr_pred ();
    gst_witness (ref_contains_pred r);
    gst_witness (region_contains_pred i);
    r

let ralloc (#a:Type) (#rel:preorder a) (i:rid) (init:a)
  :ST (mref a rel)
      (requires (fun m -> is_eternal_region i))
      (ensures (ralloc_post i init))
  = ralloc_common i init false
  
let ralloc_mm (#a:Type) (#rel:preorder a) (i:rid) (init:a)
  :ST (mmmref a rel)
      (requires (fun m -> is_eternal_region i))
      (ensures (ralloc_post i init))
  = ralloc_common i init true

(*
 * AR: 12/26: For a ref to be readable/writable/free-able,
 *            the client can either prove contains
 *            or give us enough so that we can use monotonicity to derive contains
 *)
let is_live_for_rw_in (#a:Type) (#rel:preorder a) (r:mreference a rel) (m:mem) :Type0 =
  (m `contains` r) \/
    (let i = HS.frameOf r in
     (is_eternal_region i \/ i `HS.is_above` get_tip m) /\
     (not (is_mm r)       \/ m `HS.contains_ref_in_its_region` r))

let rfree (#a:Type) (#rel:preorder a) (r:mmmref a rel)
  :ST unit
      (requires (fun m0     -> r `is_live_for_rw_in` m0))
      (ensures (fun m0 _ m1 -> m0 `contains` r /\ m1 == HS.free r m0))
  = let m0 = gst_get () in
    gst_recall (region_contains_pred (HS.frameOf r));
    gst_recall (ref_contains_pred r);
    HS.lemma_rid_ctr_pred ();
    let m1 = HS.free r m0 in
    assert (Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)));
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();    
    Heap.lemma_next_addr_free_mm (Map.sel (HS.get_hmap m0) (HS.frameOf r)) (HS.as_ref r);  //AR: to prove that next_addr in tip's heap remains same (to satisfy the predicate in mm rel)
    gst_put m1

unfold let assign_post (#a:Type) (#rel:preorder a) (r:mreference a rel) (v:a) m0 (_u:unit) m1 =
  m0 `contains` r /\ m1 == HyperStack.upd m0 r v

(**
 * Assigns, provided that the reference exists.
 * Guaranties the strongest low-level effect: Stack
 *)
let op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mreference a rel) (v:a)
  :STL unit
       (requires (fun m -> r `is_live_for_rw_in` m /\ rel (HS.sel m r) v))
       (ensures  (assign_post r v))
  = let m0 = gst_get () in
    gst_recall (region_contains_pred (HS.frameOf r));
    gst_recall (ref_contains_pred r);
    let m1 = HS.upd_tot m0 r v in
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    Heap.lemma_upd_equals_upd_tot_for_contained_refs (get_hmap m0 `Map.sel` (HS.frameOf r)) (HS.as_ref r) v;
    Heap.lemma_next_addr_upd (Map.sel (HS.get_hmap m0) (HS.frameOf r)) (HS.as_ref r) v;  //next_addr in ref's rid heap remains same
    gst_put m1

unfold let deref_post (#a:Type) (#rel:preorder a) (r:mreference a rel) m0 x m1 =
  m1 == m0 /\ m0 `contains` r /\ x == HyperStack.sel m0 r

(**
 * Dereferences, provided that the reference exists.
 * Guaranties the strongest low-level effect: Stack
 *)
let op_Bang (#a:Type) (#rel:preorder a) (r:mreference a rel)
  :Stack a (requires (fun m -> r `is_live_for_rw_in` m))
           (ensures  (deref_post r))
  = let m0 = gst_get () in
    gst_recall (region_contains_pred (HS.frameOf r));
    gst_recall (ref_contains_pred r);
    Heap.lemma_sel_equals_sel_tot_for_contained_refs (get_hmap m0 `Map.sel` (HS.frameOf r)) (HS.as_ref r);
    HS.sel_tot m0 r

let modifies_none (h0:mem) (h1:mem) = modifies Set.empty h0 h1

//   NS: This version is just fine; all the operation on mem are ghost
//       and we can rig it so that mem just get erased at the end
(**
 * Returns the current stack of heaps --- it should be erased
 *)
let get (_:unit)
  :Stack mem (requires (fun m -> True))
             (ensures (fun m0 x m1 -> m0 == x /\ m1 == m0))
  = gst_get ()

(**
 * We can only recall refs with mm bit unset, not stack refs
 *)
let recall (#a:Type) (#rel:preorder a) (r:mref a rel)
  :Stack unit (requires (fun m -> True))
              (ensures (fun m0 _ m1 -> m0 == m1 /\ m1 `contains` r))
  = gst_recall (ref_contains_pred r);
    gst_recall (region_contains_pred (HS.frameOf r))

(**
 * We can only recall eternal regions, not stack regions
 *)
let recall_region (i:rid{is_eternal_region i})
  :Stack unit (requires (fun m -> True))
              (ensures (fun m0 _ m1 -> m0 == m1 /\ i `is_in` get_hmap m1))
  = if i <> HS.root then gst_recall (region_contains_pred i)

let witness_region (i:rid)
  :Stack unit (requires (fun m0      -> is_eternal_color (color i) ==> i `is_in` get_hmap m0))
              (ensures  (fun m0 _ m1 -> m0 == m1 /\ witnessed (region_contains_pred i)))
  = gst_witness (region_contains_pred i)

let witness_hsref (#a:Type) (#rel:preorder a) (r:HS.mreference a rel)
  :ST unit (fun h0      -> h0 `HS.contains` r)
           (fun h0 _ h1 -> h0 == h1 /\ witnessed (ref_contains_pred r))
  = HS.lemma_rid_ctr_pred ();
    HS.lemma_next_addr_contained_refs_addr ();
    gst_witness (ref_contains_pred r)

(** MR witness etc. **)

(* states that p is preserved by any valid updates on r; note that h0 and h1 may differ arbitrarily elsewhere, hence proving stability usually requires that p depends only on r's content. 
 *)

type erid = r:rid{is_eternal_region r}

type m_rref (r:erid) (a:Type) (b:preorder a) = x:mref a b{HS.frameOf x = r}

unfold type stable_on_t (#a:Type0) (#rel:preorder a) (r:mreference a rel) (p:mem_predicate)
  = forall (h0 h1:mem).{:pattern (p h0); rel (HS.sel h0 r) (HS.sel h1 r)}
                  (p h0 /\ rel (HS.sel h0 r) (HS.sel h1 r)) ==> p h1

let mr_witness (#r:erid) (#a:Type) (#b:preorder a)
               (m:m_rref r a b) (p:mem_predicate)
  :ST unit (requires (fun h0      -> p h0   /\ stable_on_t m p))
           (ensures  (fun h0 _ h1 -> h0==h1 /\ witnessed p))
  = recall m;
    let p_pred (#i:erid) (#a:Type) (#b:preorder a)
               (r:m_rref i a b) (p:mem_predicate)
      :mem_predicate
      = fun m -> m `contains` r /\ p m
    in
    gst_witness (p_pred m p);
    lemma_functoriality (p_pred m p) p

let weaken_witness
  (p q:mem_predicate)
  :Lemma ((forall h. p h ==> q h) /\ witnessed p ==> witnessed q)
  = let aux () :Lemma (requires ((forall h. p h ==> q h) /\ witnessed p)) (ensures (witnessed q))
      = lemma_functoriality p q
    in
    FStar.Classical.move_requires aux ()

let testify (p:mem_predicate)
  :ST unit (requires (fun _      ->  witnessed p))
           (ensures (fun h0 _ h1 -> h0==h1 /\ p h1))
  = gst_recall p

let testify_forall (#c:Type) (#p:(c -> mem -> Type0))
  ($s:squash (forall (x:c). witnessed (p x)))
  :ST unit (requires (fun h      -> True))
           (ensures (fun h0 _ h1 -> h0==h1 /\ (forall (x:c). p x h1)))
  = W.lemma_witnessed_forall mem_rel p;
    gst_recall (fun h -> forall (x:c). p x h)

let testify_forall_region_contains_pred (#c:Type) (#p:(c -> rid))
  ($s:squash (forall (x:c). witnessed (region_contains_pred (p x))))
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\
	                          (forall (x:c). (not (HS.is_eternal_color (color (p x)))) \/ h1 `contains_region` (p x))))
  = let p' (x:c) :mem_predicate = region_contains_pred (p x) in
    let s:squash (forall (x:c). witnessed (p' x)) = () in
    testify_forall s

(*
 * Given a state predicate p, that is stable_on_t for r, this is the predicate that we witness w.r.t. mem_rel
 *)
abstract private let mm_m_predicate (#a:Type0) (#rel:preorder a) (r:mreference a rel) (p:mem_predicate)
  :mem_predicate
  = let rid = HS.frameOf r in
    fun m ->
    (HS.rid_last_component rid < HS.get_rid_ctr m) /\ (  //will help us prove that a deallocated region remains deallocated
      (m `HS.contains` r /\ p m) \/  //the ref is contained and satisfies p
      (m `contains_region` rid /\ not (m `HS.contains_ref_in_its_region` r) /\ HS.as_addr r < Heap.next_addr (HS.get_hmap m `Map.sel` rid) /\ r `HS.unused_in` m) \/  //the ref is deallocated, but its region is contained and next_addr > addr_of ref
      (not (m `contains_region` rid)))  //the region itself is not there

abstract let mm_token (#a:Type0) (#rel:preorder a) (r:mreference a rel) (p:mem_predicate)
  = witnessed (mm_m_predicate r p)

let mm_witness (#a:Type0) (#rel:preorder a) (r:mreference a rel) (p:mem_predicate)
  :ST unit (fun h0      -> HS.is_mm r /\ p h0 /\ stable_on_t r p)
           (fun h0 _ h1 -> h0 == h1 /\ mm_token r p)
  = gst_recall (ref_contains_pred r);
    HS.lemma_rid_ctr_pred ();
    HS.lemma_next_addr_contained_refs_addr ();
    gst_witness (mm_m_predicate r p)

let mm_recall (#a:Type0) (#rel:preorder a) (r:mreference a rel) (p:mem_predicate)
  :ST unit (fun h0      -> HS.is_mm r /\ h0 `HS.contains` r /\ mm_token r p)  //can't recall p unless ref is live
           (fun h0 _ h1 -> h0 == h1 /\ p h0)
  = gst_recall (mm_m_predicate r p)

type ex_rid = erid


(****** logical properties of witnessed ******)

let lemma_witnessed_constant (p:Type0)
  :Lemma (witnessed (fun (m:mem) -> p) <==> p)
  = W.lemma_witnessed_constant mem_rel p

let lemma_witnessed_nested (p:mem_predicate)
  :Lemma (witnessed (fun (m:mem) -> witnessed p) <==> witnessed p)
  = W.lemma_witnessed_nested mem_rel p;
    assert (FStar.FunctionalExtensionality.feq (fun (m:mem) -> witnessed p) (fun (m:mem) -> W.witnessed mem_rel p))

let lemma_witnessed_and (p q:mem_predicate)
  :Lemma (witnessed (fun s -> p s /\ q s) <==> (witnessed p /\ witnessed q))
  = W.lemma_witnessed_and mem_rel p q

let lemma_witnessed_or (p q:mem_predicate)
  :Lemma ((witnessed p \/ witnessed q) ==> witnessed (fun s -> p s \/ q s))
  = W.lemma_witnessed_or mem_rel p q

let lemma_witnessed_impl (p q:mem_predicate)
  :Lemma ((witnessed (fun s -> p s ==> q s) /\ witnessed p) ==> witnessed q)
  = W.lemma_witnessed_impl mem_rel p q

let lemma_witnessed_forall (#t:Type) (p:(t -> mem_predicate))
  :Lemma ((witnessed (fun s -> forall x. p x s)) <==> (forall x. witnessed (p x)))
  = W.lemma_witnessed_forall mem_rel p

let lemma_witnessed_exists (#t:Type) (p:(t -> mem_predicate))
  :Lemma ((exists x. witnessed (p x)) ==> witnessed (fun s -> exists x. p x s))
  = W.lemma_witnessed_exists mem_rel p
