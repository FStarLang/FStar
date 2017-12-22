module FStar.HyperStack.ST

open FStar.HyperStack

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

open FStar.Preorder

(* Setting up the preorder for mem *)

(* Starting the predicates that constitute the preorder *)

(* Eternal regions remain contained *)
private abstract let eternal_region_pred (m1 m2:mem) :Type0
  = forall (r:HS.rid).{:pattern (HS.is_eternal_region r); (m1.h `Map.contains` r)}
                 (HS.is_eternal_region r /\ m1.h `Map.contains` r) ==> m2.h `Map.contains` r

(* rid counter increases monotonically *)
private abstract let rid_ctr_pred (m1 m2:mem) :Type0 = m1.rid_ctr <= m2.rid_ctr

(*
 * A region r, that is:
 * (a) not contained in m1, and
 * (b) has rid last component less than m1.rid_ctr
 * 
 * remains not contained in m2
 *)
private abstract let rid_last_component_pred (m1 m2:mem) :Type0
  = forall (r:HS.rid).{:pattern (m1.h `Map.contains` r)}
                 ((~ (m1.h `Map.contains` r)) /\ rid_last_component r < m1.rid_ctr) ==>
		 (~ (m2.h `Map.contains` r))

(* Predicate for refs *)
private abstract let eternal_refs_pred (m1 m2:mem) :Type0
  = forall (a:Type) (rel:preorder a) (r:HS.mreference a rel).
      {:pattern (m1 `HS.contains` r)}
      if is_mm r then True
      else
        if m1 `HS.contains` r then
	  if is_eternal_region (HS.frameOf r) then m2 `HS.contains` r /\ rel (HS.sel m1 r) (HS.sel m2 r)
	  else if m2.h `Map.contains` (HS.frameOf r) then m2 `HS.contains` r /\ rel (HS.sel m1 r) (HS.sel m2 r)
	  else True
	else True

(* The preorder is the conjunction of above predicates *)
private abstract let mem_rel :relation mem
  = fun (m1 m2:mem) ->
    eternal_region_pred m1 m2 /\ rid_ctr_pred m1 m2 /\ rid_last_component_pred m1 m2 /\ eternal_refs_pred m1 m2
private abstract let mem_pre :preorder mem =
  HS.lemma_rid_ctr_pred ();
  mem_rel

type mem_predicate = mem -> Type0

(* Predicates that we will witness with regions and refs *)
abstract let region_contains_pred (r:HS.rid) :mem_predicate
  = fun m -> (not (HS.is_eternal_region r)) \/ m.h `Map.contains` r

abstract let ref_contains_pred (#a:Type) (#rel:preorder a) (r:HS.mreference a rel) :mem_predicate
  = fun m -> rid_last_component (HS.frameOf r) < m.rid_ctr /\
          (HS.is_mm r \/ (not (m.h `Map.contains` (HS.frameOf r)) \/ m `HS.contains` r))

(***** Global ST (GST) effect with put, get, witness, and recall *****)

new_effect GST = STATE_h mem

let gst_pre           = st_pre_h mem
let gst_post' (a:Type) (pre:Type) = st_post_h' mem a True
let gst_post (a:Type) = st_post_h mem a
let gst_wp (a:Type)   = st_wp_h mem a

unfold let lift_div_gst (a:Type0) (wp:pure_wp a) (p:gst_post a) (h:mem) = wp (fun a -> p a h)
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
       
abstract let stable (p:mem_predicate) =
  forall (h1:mem) (h2:mem).{:pattern (mem_rel h1 h2)} (p h1 /\ mem_rel h1 h2) ==> p h2

assume type witnessed: mem_predicate -> Type0

(* TODO: we should derive these using DM4F *)
assume val gst_get: unit    -> GST mem (fun p h0 -> p h0 h0)
assume val gst_put: h1:mem -> GST unit (fun p h0 -> mem_rel h0 h1 /\ p () h1)

assume val gst_witness: p:mem_predicate -> GST unit (fun post h0 -> p h0 /\ stable p /\ (witnessed p ==> post () h0))
assume val gst_recall:  p:mem_predicate -> GST unit (fun post h0 -> witnessed p /\ (p h0 ==> post () h0))

assume val lemma_functoriality
  (p:mem_predicate{witnessed p}) (q:mem_predicate{(forall (h:mem). p h ==> q h)})
  : Lemma (ensures (witnessed q))

let st_pre   = gst_pre
let st_post' = gst_post'
let st_post  = gst_post
let st_wp    = gst_wp

new_effect STATE = GST

unfold let lift_gst_state (a:Type0) (wp:gst_wp a) = wp
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

(**
   Effect of stacked based code: the 'equal_domains' clause enforces that
   - both mem have the same tip
   - both mem reference the same heaps (their map: rid -> heap have the same domain)
   - in each region id, the corresponding heaps contain the same references on both sides
 *)
effect Stack (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ equal_domains h h1) ==> p a h1)) (* WP *)

(**
   Effect of heap-based code.
   - assumes that the stack is empty (tip = root)
   - corresponds to the HyperHeap ST effect
   - can call to Stack and ST code freely
   - respects the stack invariant: the stack has to be empty when returning
*)
effect Heap (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ h.tip = HS.root /\ h1.tip = HS.root ) ==> p a h1)) (* WP *)

(**
  Effect of low-level code:
  - maintains the allocation invariant on the stack: no allocation unless in a new frame that has to be popped before returning
  - not constraints on heap allocation
*)
effect ST (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ equal_stack_domains h h1) ==> p a h1)) (* WP *)

effect St (a:Type) = ST a (fun _ -> True) (fun _ _ _ -> True)

let inline_stack_inv h h' : GTot Type0 =
  (* The frame invariant is enforced *)
  h.tip = h'.tip
  (* The heap structure is unchanged *)
  /\ Map.domain h.h == Map.domain h'.h
  (* Any region that is not the tip has no seen any allocation *)
  /\ (forall (r:HS.rid). {:pattern (Map.contains h.h r)} (r <> h.tip /\ Map.contains h.h r)
       ==> Heap.equal_dom (Map.sel h.h r) (Map.sel h'.h r) /\
           Map.contains h'.h r)

(**
   Effect that indicates to the Kremlin compiler that allocation may occur in the caller's frame.
   In other terms, the backend has to unfold the body into the caller's body.
   This effect maintains the stack AND the heap invariant: it can be inlined in the Stack effect
   function body as well as in a Heap effect function body
   *)
effect StackInline (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ is_stack_region h.tip /\ (forall a h1. (pre h /\ post h a h1 /\ inline_stack_inv h h1) ==> p a h1)) (* WP *)

let inline_inv h h' : GTot Type0 =
  (* The stack invariant is enforced *)
  h.tip = h'.tip
  (* No frame may have received an allocation but the tip *)
  /\ (forall (r:HS.rid). {:pattern (is_stack_region r)}(is_stack_region r /\ r `is_strictly_above` h.tip)
       ==> Heap.equal_dom (Map.sel h.h r) (Map.sel h'.h r))

(**
   Effect that indicates to the Kremlin compiler that allocation may occur in the caller's frame.
   In other terms, the backend has to unfold the body into the caller's body.
   This effect only maintains the stack invariant: the tip is left unchanged and no allocation
   may occurs in the stack lower than the tip.
   Region allocation is not constrained.
   Heap allocation is not constrained.
   *)
effect Inline (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ inline_inv h h1) ==> p a h1)) (* WP *)

(**
    TODO:
    REMOVE AS SOON AS CONSENSUS IS REACHED ON NEW LOW EFFECT NAMES
  *)
effect STL (a:Type) (pre:st_pre) (post: (m0:mem -> Tot (st_post' a (pre m0)))) = Stack a pre post

sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:mem) -> wp (fun a -> p a h)


(*
 * AR: A few caveats:
 * (a) The clients should now open HyperStack.ST after the memory model files (as with Heap and FStar.ST).
 * (b) When the clients get rid from this interface, they will get witnessed predicates.
 *     But if we directly get an id from the HH map, then we don't get these.
 * (c) Similar thing happens with mem, there is a refinement that we attach to mem, but that could
 *     probably be moved to HyperStack mem itself.
 *)
// unfold let rid_refinement (r:HS.rid)
//   = r == HS.root                \/
//     (not (is_eternal_region r)) \/
//     witnessed (region_contains_pred r)
// type rid = r:HS.rid{rid_refinement r}
type rid = HS.rid

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

(*
 * AR: The change to using ST.rid may not be that bad itself,
 *     since subtyping should take care of most instances in the client usage.
 *     However, one case where it could be an issue is modifies clauses that use
 *     Set.set rid.
 *)


(**
   Pushes a new empty frame on the stack
   *)
let push_frame (_:unit) :Unsafe unit (requires (fun m -> True)) (ensures (fun (m0:mem) _ (m1:mem) -> fresh_frame m0 m1))
  = let m0 = gst_get () in
    let m1 = HS.push_frame m0 in
    gst_put m1

(**
   Removes old frame from the stack
   *)
let pop_frame (_:unit)
  :Unsafe unit
  (requires (fun m -> poppable m))
  (ensures (fun (m0:mem) _ (m1:mem) -> poppable m0 /\ m1==pop m0 /\ popped m0 m1))
  = let m1 = pop (gst_get ()) in
    gst_put m1

let salloc_post (#a:Type) (#rel:preorder a) (init:a) (m0:mem)
                (s:mreference a rel{is_stack_region (frameOf s)}) (m1:mem)
  = is_stack_region m0.tip              /\
    Map.domain m0.h == Map.domain m1.h  /\
    m0.tip = m1.tip                     /\
    frameOf s   = m1.tip                /\
    HS.fresh_ref s m0 m1                /\  //it's a fresh reference in the top frame
    m1 == HyperStack.upd m0 s init  //and it's been initialized

private let salloc_common (#a:Type) (#rel:preorder a) (init:a) (mm:bool)
  :StackInline (mreference a rel)
  (requires (fun m       -> is_stack_region m.tip))
  (ensures  (fun m0 s m1 -> is_stack_region (HS.frameOf s) /\ salloc_post init m0 s m1 /\ is_mm s == mm))
  = let m0 = gst_get () in
    let r, m1 = HS.alloc rel m0.tip init mm m0 in
    gst_put m1;
    assert (Set.equal (Map.domain m0.h) (Map.domain m1.h));
    HS.lemma_rid_ctr_pred ();  //AR: to prove that rid_last_component of r.id is < rid_ctr
    gst_witness (ref_contains_pred r);
    gst_witness (region_contains_pred (HS.frameOf r));
    r

(**
     Allocates on the top-most stack frame
     *)
let salloc (#a:Type) (#rel:preorder a) (init:a)
  :StackInline (mstackref a rel)
  (requires (fun m -> is_stack_region m.tip))
  (ensures salloc_post init)
  = salloc_common init false
  
let salloc_mm (#a:Type) (#rel:preorder a) (init:a)
  : StackInline (mmmstackref a rel)
  (requires (fun m -> is_stack_region m.tip))
  (ensures salloc_post init)
  = salloc_common init true

let sfree (#a:Type) (#rel:preorder a) (r:mmmstackref a rel)
  :StackInline unit
   (requires (fun m0 -> frameOf r = m0.tip /\ m0 `contains` r))
   (ensures (fun m0 _ m1 -> m0 `contains` r /\ m1 == HS.free r m0))
  = let m0 = gst_get () in
    let m1 = HS.free r m0 in
    assert (Set.equal (Map.domain m0.h) (Map.domain m1.h));
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();    
    gst_put m1

#set-options "--z3rlimit 10"
let new_region (r0:rid)
  :ST rid
      (requires (fun m        -> is_eternal_region r0 /\
                              (r0 == HS.root \/ witnessed (region_contains_pred r0))))
      (ensures  (fun m0 r1 m1 ->
                 r1 `HH.extends` r0                  /\
                 HS.fresh_region r1 m0 m1            /\
		 HS.color r1 = HS.color r0           /\
		 witnessed (region_contains_pred r1) /\
		 m1.h == Map.upd m0.h r1 Heap.emp    /\
		 m1.tip = m0.tip))
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
      (requires (fun m       -> is_eternal_color c /\ is_eternal_region r0 /\
                             (r0 == HS.root \/ witnessed (region_contains_pred r0))))
      (ensures (fun m0 r1 m1 ->
                r1 `HH.extends` r0                  /\
                HS.fresh_region r1 m0 m1            /\
	        HS.color r1 = c                     /\
		witnessed (region_contains_pred r1) /\
	        m1.h == Map.upd m0.h r1 Heap.emp    /\
		m1.tip = m0.tip))
  = if r0 <> HS.root then gst_recall (region_contains_pred r0);  //recall containment of r0
    HS.lemma_rid_ctr_pred ();
    let m0 = gst_get () in
    let new_rid, m1 = HS.new_eternal_region m0 r0 (Some c) in
    gst_put m1;
    gst_witness (region_contains_pred new_rid);
    new_rid

unfold let ralloc_post (#a:Type) (#rel:preorder a) (i:rid) (init:a) (m0:mem)
                       (x:mreference a rel{is_eternal_region (frameOf x)}) (m1:mem) =
    let region_i = Map.sel m0.h i in
    as_ref x `Heap.unused_in` region_i /\
    i `is_in` m0.h                     /\
    i = frameOf x                      /\
    m1 == upd m0 x init                      

private let ralloc_common (#a:Type) (#rel:preorder a) (i:rid) (init:a) (mm:bool)
  :ST (mreference a rel)
      (requires (fun m       -> is_eternal_region i /\ (i == HS.root \/ witnessed (region_contains_pred i))))
      (ensures  (fun m0 r m1 -> is_eternal_region (frameOf r) /\ ralloc_post i init m0 r m1 /\ is_mm r == mm))
  = if i <> HS.root then gst_recall (region_contains_pred i);
    let m0 = gst_get () in
    let r, m1 = HS.alloc rel i init mm m0 in
    gst_put m1;
    assert (Set.equal (Map.domain m0.h) (Map.domain m1.h));
    HS.lemma_rid_ctr_pred ();
    gst_witness (ref_contains_pred r);
    gst_witness (region_contains_pred i);
    r
#reset-options

let ralloc (#a:Type) (#rel:preorder a) (i:rid) (init:a)
  :ST (mref a rel)
      (requires (fun m -> is_eternal_region i /\ (i == HS.root \/ witnessed (region_contains_pred i))))
      (ensures (ralloc_post i init))
  = ralloc_common i init false
  
let ralloc_mm (#a:Type) (#rel:preorder a) (i:rid) (init:a)
  :ST (mmmref a rel)
      (requires (fun m -> is_eternal_region i /\ (i == HS.root \/ witnessed (region_contains_pred i))))
      (ensures (ralloc_post i init))
  = ralloc_common i init true

let is_live_for_rw_in (#a:Type) (#rel:preorder a) (r:mreference a rel) (m:mem) :GTot bool =
  (m `contains` r) ||
    (let i = HS.frameOf r in
     (is_eternal_region i || i `HS.is_above` m.tip) &&
     (not (is_mm r)       || m `HS.contains_ref_in_its_region` r))

let rfree (#a:Type) (#rel:preorder a) (r:mmmref a rel)
  :ST unit
      (requires (fun m0     -> r `is_live_for_rw_in` m0))
      (ensures (fun m0 _ m1 -> m0 `contains` r /\ m1 == HS.free r m0))
  = let m0 = gst_get () in
    gst_recall (region_contains_pred (HS.frameOf r));
    gst_recall (ref_contains_pred r);
    HS.lemma_rid_ctr_pred ();
    let m1 = HS.free r m0 in
    assert (Set.equal (Map.domain m0.h) (Map.domain m1.h));
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();    
    gst_put m1

unfold let assign_post (#a:Type) (#rel:preorder a) (r:mreference a rel) (v:a) m0 (_u:unit) m1 =
  m0 `contains` r /\ m1 == HyperStack.upd m0 r v

(**
   Assigns, provided that the reference exists.
   Guaranties the strongest low-level effect: Stack
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
    gst_put m1

unfold let deref_post (#a:Type) (#rel:preorder a) (r:mreference a rel) m0 x m1 =
  m1 == m0 /\ m0 `contains` r /\ x == HyperStack.sel m0 r

(**
   Dereferences, provided that the reference exists.
   Guaranties the strongest low-level effect: Stack
   *)
(*
 * AR: making the precondition as weak_contains.
 *)
let op_Bang (#a:Type) (#rel:preorder a) (r:mreference a rel)
  :Stack a (requires (fun m -> r `is_live_for_rw_in` m))
           (ensures  (deref_post r))
  = let m0 = gst_get () in
    gst_recall (region_contains_pred (HS.frameOf r));
    gst_recall (ref_contains_pred r);
    HS.sel_tot m0 r

let modifies_none (h0:mem) (h1:mem) = modifies Set.empty h0 h1

module G = FStar.Ghost

//   NS: This version is just fine; all the operation on mem are ghost
//       and we can rig it so that mem just get erased at the end
(**
    Returns the current stack of heaps --- it should be erased
    *)
let get (_:unit)
  :Stack mem (requires (fun m -> True))
             (ensures (fun m0 x m1 -> m0==x /\ m1==m0))
  = gst_get ()

(**
   We can only recall refs with mm bit unset, not stack refs
   *)
let recall (#a:Type) (#rel:preorder a) (r:mref a rel)
  :Stack unit (requires (fun m -> True))
              (ensures (fun m0 _ m1 -> m0==m1 /\ m1 `contains` r))
  = gst_recall (ref_contains_pred r);
    gst_recall (region_contains_pred (HS.frameOf r))

(**
   We can only recall eternal regions, not stack regions
   *)
let recall_region (i:rid{is_eternal_region i})
  :Stack unit (requires (fun m -> i == HS.root \/ witnessed (region_contains_pred i)))
              (ensures (fun m0 _ m1 -> m0==m1 /\ i `is_in` m1.h))
  = if i <> HS.root then gst_recall (region_contains_pred i)

let witness_region (i:rid)
  :Stack unit (requires (fun m0      -> is_eternal_region i ==> i `is_in` m0.h))
              (ensures  (fun m0 _ m1 -> m0 == m1 /\ witnessed (region_contains_pred i)))
  = gst_witness (region_contains_pred i)

let witness_hsref (#a:Type) (#rel:preorder a) (r:HS.mreference a rel)
  :ST unit (fun h0      -> h0 `HS.contains` r)
           (fun h0 _ h1 -> h0 == h1 /\ witnessed (ref_contains_pred r))
  = HS.lemma_rid_ctr_pred ();
    gst_witness (ref_contains_pred r)

(* Tests *)
val test_do_nothing: int -> Stack int
  (requires (fun h -> True))
  (ensures (fun h _ h1 -> True))
let test_do_nothing x =
  push_frame();
  pop_frame ();
  x

val test_do_something: #rel:preorder int -> s:mstackref int rel -> Stack int
  (requires (fun h     -> contains h s))
  (ensures (fun h r h1 -> contains h s /\ r = sel h s))
let test_do_something #rel s =
  push_frame();
  let res = !s in
  pop_frame ();
  res

val test_do_something_else: #rel:preorder int -> s:mstackref int rel -> v:int -> Stack unit
  (requires (fun h     -> contains h s /\ rel (HS.sel h s) v))
  (ensures (fun h r h1 -> contains h1 s /\ v = sel h1 s))
let test_do_something_else #rel s v =
  push_frame();
  s := v;
  pop_frame ()

val test_allocate: unit -> Stack unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let test_allocate () =
  push_frame();
  let x :stackref int = salloc 1 in
  x := 2;
  pop_frame ()

val test_nested_stl: unit -> Stack unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let test_nested_stl () =
  let x = test_do_nothing 0 in ()

val test_nested_stl2: unit -> Stack unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let test_nested_stl2 () =
  push_frame ();
  let x = test_do_nothing 0 in
  pop_frame ()

(* Testing mix of Heap and Stack code *)
val test_stack: int -> Stack int
  (requires (fun h -> True))
  (ensures (fun h _ h1 -> modifies Set.empty h h1))
let test_stack x =
  push_frame();
  let s :stackref int = salloc x in
  s := (1 + x);
  pop_frame ();
  x

val test_stack_with_long_lived: #rel:preorder int -> s:mreference int rel -> Stack unit
  (requires (fun h -> contains h s /\ rel (HS.sel h s) (HS.sel h s + 1)))
  (ensures  (fun h0 _ h1 -> contains h1 s /\ sel h1 s = (sel h0 s) + 1 /\
                         modifies (Set.singleton (frameOf s)) h0 h1))
#set-options "--z3rlimit 10"
let test_stack_with_long_lived #rel s =
  push_frame();
  let _ = test_stack !s in
  s := !s + 1;
  pop_frame()
#reset-options

val test_heap_code_with_stack_calls: unit -> Heap unit
  (requires (fun h -> heap_only h))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton h0.tip) h0 h1 ))
let test_heap_code_with_stack_calls () =
  let h = get () in
  // How is the following not known ?
  HH.root_has_color_zero ();
  let s :ref int = ralloc h.tip 0 in
  test_stack_with_long_lived s;
  s := 1;
  ()

val test_heap_code_with_stack_calls_and_regions: unit -> Heap unit
  (requires (fun h -> heap_only h))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton h0.tip) h0 h1 ))
let test_heap_code_with_stack_calls_and_regions () =
  let h = get() in
  let color = 0 in
  HH.root_has_color_zero ();
  let new_region = new_colored_region h.tip color in
  let s :ref int = ralloc new_region 1 in
  test_stack_with_long_lived s; // STStack call
  test_heap_code_with_stack_calls (); // STHeap call
  ()

val test_lax_code_with_stack_calls_and_regions: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton HS.root) h0 h1 ))
let test_lax_code_with_stack_calls_and_regions () =
  push_frame();
  let color = 0 in
  HH.root_has_color_zero ();
  let new_region = new_colored_region HS.root color in
  let s :ref int = ralloc new_region 1 in
  test_stack_with_long_lived s; // Stack call
  pop_frame()

val test_lax_code_with_stack_calls_and_regions_2: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton HS.root) h0 h1 ))
#set-options "--z3rlimit 10"
let test_lax_code_with_stack_calls_and_regions_2 () =
  push_frame();
  let color = 0 in
  HH.root_has_color_zero ();
  let new_region = new_colored_region HS.root color in
  let s :ref int = ralloc new_region 1 in
  test_stack_with_long_lived s; // Stack call
  test_lax_code_with_stack_calls_and_regions (); // ST call
  pop_frame()
#reset-options

val test_to_be_stack_inlined: unit -> StackInline (reference int)
  (requires (fun h -> is_stack_region h.tip))
  (ensures  (fun h0 r h1 -> ~(contains h0 r) /\ contains h1 r /\ sel h1 r = 2))
let test_to_be_stack_inlined () =
  let r :stackref int = salloc 0 in
  r := 2;
  r

val test_stack_function_with_inline: unit -> Stack int
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))
let test_stack_function_with_inline () =
  push_frame();
  let x = test_to_be_stack_inlined () in
  let y = !x + !x in
  pop_frame();
  y

val test_st_function_with_inline: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))
let test_st_function_with_inline () =
  push_frame();
  let x = test_to_be_stack_inlined () in
  let y = !x + !x in
  pop_frame();
  ()

val test_to_be_inlined: unit -> Inline (reference int * reference int)
  (requires (fun h -> is_stack_region h.tip))
  (ensures  (fun h0 r h1 -> True))
let test_to_be_inlined () =
  let r :stackref int = salloc 0 in
  HH.root_has_color_zero ();
  let region = new_region HS.root in
  let r' = ralloc region 1 in
  r := 2;
  r' := 3;
  r,r'

val test_st_function_with_inline_2: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))
let test_st_function_with_inline_2 () =
  push_frame();
  let x = test_to_be_stack_inlined () in
  let r, r' = test_to_be_inlined () in
  pop_frame();
  ()

val with_frame: #a:Type -> #pre:st_pre -> #post:(mem -> Tot (st_post a)) -> $f:(unit -> Stack a pre post)
	     -> Stack a (fun s0 -> forall (s1:mem). fresh_frame s0 s1 ==> pre s1)
		     (fun s0 x s1 ->
			exists (s0' s1':mem). fresh_frame s0 s0'
			         /\ poppable s0'
				 /\ post s0' x s1'
				 /\ equal_domains s0' s1'
				 /\ s1 == pop s1')
let with_frame #a #pre #post f =
  push_frame();
  let x = f() in
  pop_frame();
  x

let test_with_frame (x:stackref int) (v:int)
  : Stack unit (requires (fun m -> contains m x))
	       (ensures (fun m0 _ m1 -> modifies (Set.singleton (frameOf x)) m0 m1 /\ sel m1 x = v))
 = admit () //with_frame (fun _ -> x := v)


let as_requires (#a:Type) (wp:st_wp a) = wp (fun x s -> True)
let as_ensures (#a:Type) (wp:st_wp a) = fun s0 x s1 -> wp (fun y s1' -> y=!=x \/ s1=!=s1') s0

assume val as_stack: #a:Type -> #wp:st_wp a -> $f:(unit -> STATE a wp) ->
	   Pure (unit -> Stack a (as_requires wp)
			      (as_ensures wp))
	        (requires (forall s0 x s1. as_ensures wp s0 x s1 ==> equal_domains s0 s1))
 	        (ensures (fun x -> True))

val mm_tests: unit -> Unsafe unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let mm_tests _ =
  let _ = push_frame () in

  let r1 :mmstackref int = salloc_mm 2 in

  //check that the heap contains the reference
  let m = get () in
  let h = Map.sel m.h m.tip in
  let _ = assert (Heap.contains h (as_ref r1)) in

  let _ = !r1 in

  let _ = sfree r1 in

  //this fails because the ref has been freed
  //let _ = !r1 in

  //check that the heap does not contain the reference
  let m = get () in
  let h = Map.sel m.h m.tip in
  let _ = assert (~ (Heap.contains h (as_ref r1))) in

  let r2 :mmstackref int = salloc_mm 2 in
  let _ = pop_frame () in

  //this fails because the reference is no longer live
  //let _ = sfree r2 in

  let id = new_region HS.root in

  let r3 :mmref int = ralloc_mm id 2 in
  let _ = !r3 in
  let _ = rfree r3 in

  //check that the heap does not contain the reference
  let m = get () in
  let h = Map.sel m.h id in
  let _ = assert (~ (Heap.contains h (as_ref r3))) in

  //this fails because the reference is no longer live
  //let _ = !r3 in

  //this fails because recall of mm refs is not allowed
  //let _ = recall r3 in
  ()



(** MR witness etc. **)

(* states that p is preserved by any valid updates on r; note that h0 and h1 may differ arbitrarily elsewhere, hence proving stability usually requires that p depends only on r's content. 
*)

type erid = r:rid{is_eternal_region r}

type m_rref (r:erid) (a:Type) (b:preorder a) = x:mref a b{HS.frameOf x = r}

unfold type stable_on_t (#i:erid) (#a:Type) (#b:preorder a)
                        (r:m_rref i a b) (p:mem_predicate)
  = forall h0 h1.{:pattern (p h0); b (HS.sel h0 r) (HS.sel h1 r)}
            (p h0 /\ b (HS.sel h0 r) (HS.sel h1 r)) ==> p h1

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
