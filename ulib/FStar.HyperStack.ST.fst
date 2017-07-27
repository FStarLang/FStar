module FStar.HyperStack.ST
open FStar.Preorder
open FStar.HyperStack
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module Set = FStar.Set

(***** Global ST (GST) effect with put, get, witness, and recall *****)

new_effect GST = STATE_h mem

let gst_pre           = st_pre_h mem
let gst_post (a:Type) = st_post_h mem a
let gst_wp (a:Type)   = st_wp_h mem a

unfold let lift_div_gst (a:Type0) (wp:pure_wp a) (p:gst_post a) (h:mem) = wp (fun a -> p a h)
sub_effect DIV ~> GST = lift_div_gst

let ref_requires (#a:Type) (#rel:preorder a) (r:mreference a rel) (h:mem) =
  ~(is_mm r) /\
  (* (is_mm r ==> h `contains` r) /\ *)
  (is_stack_region r.id /\ ~ (is_mm r) ==> r.id `is_above` h.tip)

let mem_rel0 (h1:mem) (h2:mem) =
  (forall (a:Type0) (rel:preorder a) (r:mreference a rel).
    h1 `contains` r /\ ref_requires r h2 ==> (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))) /\
  (forall (i:HH.rid). Map.contains h1.h i ==> Map.contains h2.h i) /\
  (forall (i:HH.rid). ~(i `is_alive` h1) ==> ~(i `is_alive` h2))

let mem_rel : preorder mem = mem_rel0

assume val gst_get: unit    -> GST mem (fun p h0 -> p h0 h0)
assume val gst_put: h1:mem -> GST unit (fun p h0 -> mem_rel h0 h1 /\ p () h1)

type mem_predicate = mem -> Type0

let stable (p:mem_predicate) =
  forall (h1:mem) (h2:mem). (p h1 /\ mem_rel h1 h2) ==> p h2

assume type witnessed: (p:mem_predicate{stable p}) -> Type0

assume val gst_witness: p:mem_predicate -> GST unit (fun post h0 -> stable p /\ p h0 /\ (witnessed p ==> post () h0))
assume val gst_recall:  p:mem_predicate -> GST unit (fun post h0 -> stable p /\ witnessed p /\ (p h0 ==> post () h0))


(**
    WARNING: this effect is unsafe, for C/C++ extraction it shall only be used by
    code that would later extract to OCaml or by library functions
    *)
effect Unsafe (a:Type) (pre:gst_pre) (post: (mem -> Tot (gst_post a))) =
  GST a
    (fun (p:gst_post a) (h:mem) -> pre h /\ (forall a h1. pre h /\ post h a h1 ==> p a h1)) (* WP *)

(**
   Effect of stacked based code: the 'equal_domains' clause enforces that
   - both mem have the same tip
   - both mem reference the same heaps (their map: rid -> heap have the same domain)
   - in each region id, the corresponding heaps contain the same references on both sides
 *)
effect Stack (a:Type) (pre:gst_pre) (post: (mem -> Tot (gst_post a))) =
  GST a
    (fun (p:gst_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ equal_domains h h1) ==> p a h1)) (* WP *)

(**
   Effect of heap-based code.
   - assumes that the stack is empty (tip = root)
   - corresponds to the HyperHeap ST effect
   - can call to Stack and ST code freely
   - respects the stack invariant: the stack has to be empty when returning
*)
effect Heap (a:Type) (pre:gst_pre) (post: (mem -> Tot (gst_post a))) =
  GST a
    (fun (p:gst_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ h.tip = HH.root /\ h1.tip = HH.root ) ==> p a h1)) (* WP *)

(**
  Effect of low-level code:
  - maintains the allocation invariant on the stack: no allocation unless in a new frame that has to be popped before returning
  - not constraints on heap allocation
*)
effect ST (a:Type) (pre:gst_pre) (post: (mem -> Tot (gst_post a))) =
  GST a
    (fun (p:gst_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ equal_stack_domains h h1) ==> p a h1)) (* WP *)

effect St (a:Type) = ST a (fun _ -> True) (fun _ _ _ -> True)

let inline_stack_inv h h' : GTot Type0 =
  (* The frame invariant is enforced *)
  h.tip == h'.tip
  (* The heap structure is unchanged *)
  /\ Map.domain h.h == Map.domain h'.h
  (* Any region that is not the tip has no seen any allocation *)
  /\ (forall (r:HH.rid). {:pattern (Map.contains h.h r)} (r =!= h.tip /\ r `is_in` h.h)
       ==> Heap.equal_dom (h `at` r) (h' `at` r))

(**
   Effect that indicates to the Kremlin compiler that allocation may occur in the caller's frame.
   In other terms, the backend has to unfold the body into the caller's body.
   This effect maintains the stack AND the heap invariant: it can be inlined in the Stack effect
   function body as well as in a Heap effect function body
   *)
effect StackInline (a:Type) (pre:gst_pre) (post: (mem -> Tot (gst_post a))) =
  GST a
    (fun (p:gst_post a) (h:mem) -> pre h /\ is_stack_region h.tip /\ (forall a h1. (pre h /\ post h a h1 /\ inline_stack_inv h h1) ==> p a h1)) (* WP *)

let inline_inv h h' : GTot Type0 =
  (* The stack invariant is enforced *)
  h.tip == h'.tip
  (* No frame may have received an allocation but the tip *)
  /\ (forall (r:HH.rid). {:pattern (is_stack_region r)}(is_stack_region r /\ r `is_strictly_above` h.tip)
       ==> Heap.equal_dom (h `at` r) (h' `at` r))

(**
   Effect that indicates to the Kremlin compiler that allocation may occur in the caller's frame.
   In other terms, the backend has to unfold the body into the caller's body.
   This effect only maintains the stack invariant: the tip is left unchanged and no allocation
   may occurs in the stack lower than the tip.
   Region allocation is not constrained.
   Heap allocation is not constrained.
   *)
effect Inline (a:Type) (pre:gst_pre) (post: (mem -> Tot (gst_post a))) =
  GST a
    (fun (p:gst_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ inline_inv h h1) ==> p a h1)) (* WP *)

(**
    TODO:
    REMOVE AS SOON AS CONSENSUS IS REACHED ON NEW LOW EFFECT NAMES
  *)
effect STL (a:Type) (pre:gst_pre) (post: (mem -> Tot (gst_post a))) = Stack a pre post

sub_effect
  DIV   ~> GST = fun (a:Type) (wp:pure_wp a) (p:gst_post a) (h:mem) -> wp (fun a -> p a h)

let region_allocated_pred (i:HH.rid) : p:mem_predicate{stable p} =
  fun (m:mem) -> Map.contains m.h i

let rid = i:HH.rid{witnessed (region_allocated_pred i)}
let recall_weak_live_region (r:rid)
  : GST unit (fun (p:gst_post unit) (m:mem) -> weak_live_region m r /\ (r `is_in` m.h ==> p () m))
= gst_witness (region_allocated_pred HH.root) ; gst_recall (region_allocated_pred r)

let valid_ref (#a:Type) (#rel:preorder a) (r:mreference a rel) : p:mem_predicate{stable p} =
  fun (m:mem) ->
    region_allocated_pred r.id m /\
    (not (is_mm r) /\ r.id `is_alive` m ==> HH.contains_ref m.h r.ref)

type reference (a:Type) = r:reference a{witnessed(valid_ref r)}

let stackref (a:Type) = s:stackref a{witnessed(valid_ref s)}
let ref (a:Type) = r:ref a{witnessed(valid_ref r)}

let mmstackref (a:Type) = r:mmstackref a{witnessed(valid_ref r)}
let mmref (a:Type) = r:mmref a{witnessed(valid_ref r)}

type s_ref (i:rid) (a:Type) = s:s_ref i a{witnessed(valid_ref s)}

(* TODO : We need to provide access to the internal representation of HH.rid in order to implement this fnction... *)
assume val fresh_child : r:HH.rid -> c:int ->
  GST rid
    (fun (p:gst_post rid) (m0:mem) ->
      r `is_in` m0.h /\
      (forall (r':rid) m1. r' =!= HH.root /\ r `is_in` m0.h /\ HH.parent r' == r /\ HH.color r' == c /\
        m1.h == Map.upd m0.h r' HH.emp
      /\ m1.tip == m0.tip
      /\ HH.fresh_region r' m0.h m1.h ==> p r' m1))

(**
   Pushes a new empty frame on the stack
   *)
val push_frame: unit -> Unsafe unit
  (requires (fun m -> True))
  (ensures (fun (m0:mem) _ (m1:mem) -> fresh_frame m0 m1))
let push_frame () =
  let m0 = gst_get () in
  let tip = fresh_child m0.tip 1 in
  let h = Map.upd m0.h tip HH.emp in
  let m1 = HS h tip in
  gst_put m1

(**
   Removes old frame from the stack
   *)
val pop_frame: unit -> Unsafe unit
  (requires (fun m -> poppable m))
  (ensures (fun (m0:mem) _ (m1:mem) -> poppable m0 /\ m1==pop m0 /\ popped m0 m1))
let pop_frame () =
  let m0 = gst_get () in
  let m1 = pop m0 in
  assert (popped m0 m1) ;
  assert (mem_rel m0 m1) ;
  gst_put m1

let salloc_post (#a:Type) (init:a) (m0:mem) (s:reference a{is_stack_region s.id}) (m1:mem) =
      is_stack_region m0.tip
    /\ Map.domain m0.h == Map.domain m1.h
    /\ m0.tip == m1.tip
    /\ s.id   == m1.tip
    /\ HH.fresh_rref s.ref m0.h m1.h         //it's a fresh reference in the top frame
    /\ m1==HyperStack.upd m0 s init          //and it's been initialized

(**
     Allocates on the top-most stack frame
     *)
private
let lemma_upd_existing_rid_idempotent (i:HH.rid) (m:mem)
  : Lemma (requires (i `is_in` m.h))
    (ensures (Map.domain m.h `Set.union` Set.singleton i == Map.domain m.h))
= Set.lemma_mem_idempotent_union (Map.domain m.h) i

private
let lemma_upd_tip_idempotent (m:mem)
  : Lemma (Map.domain m.h `Set.union` Set.singleton m.tip == Map.domain m.h)
= Set.lemma_mem_idempotent_union (Map.domain m.h) m.tip

private
val salloc_maybe_mm: #a:Type -> init:a -> mm:bool -> StackInline (s:reference a{is_stack_region s.id})
  (requires (fun m -> is_stack_region m.tip))
  (ensures (fun m0 s m1 -> salloc_post init m0 s m1 /\ is_mm s == mm))
let salloc_maybe_mm #a init mm =
  let m0 = gst_get () in
  let r, h = HH.alloc m0.tip (Heap.trivial_preorder a) m0.h init mm in
  HH.lemma_alloc m0.tip (Heap.trivial_preorder a) m0.h init mm ;
  lemma_upd_tip_idempotent m0;
  let m1 = HS h m0.tip in
  gst_put m1 ;
  let s = MkRef m0.tip r in
  gst_witness (valid_ref s) ;
  s

val salloc: #a:Type -> init:a -> StackInline (stackref a)
  (requires (fun m -> is_stack_region m.tip))
  (ensures salloc_post init)
let salloc #a init =
  salloc_maybe_mm #a init false

val salloc_mm: #a:Type -> init:a -> StackInline (mmstackref a)
  (requires (fun m -> is_stack_region m.tip))
  (ensures salloc_post init)
let salloc_mm #a init =
  salloc_maybe_mm #a init true


let remove_reference (#a:Type) (r:reference a) (m:mem{m `contains` r /\ is_mm r}) : Tot mem =
  HS (HH.free_mm m.h r.ref) m.tip

let ref_requiresminusmmstackref (#a:Type) (#rel:preorder a) (r:mreference a rel) (h:mem) =
  is_eternal_region r.id /\ ~(is_mm r) \/
  (is_eternal_region r.id /\ is_mm r /\ h `contains` r) \/
  (is_stack_region r.id /\ is_mm r /\ h `contains` r)

val lemma_distinct_addrs_distinct_mm
    (#a #b:Type0) (#rel1:preorder a) (#rel2: preorder b) (m:mem) (r1:mreference a rel1) (r2:mreference b rel2)
    :Lemma (requires (is_mm r1 =!= is_mm r2 /\ r1.id == r2.id /\ m.h `HH.contains_ref` r1.ref /\ m.h `HH.contains_ref` r2.ref))
            (ensures (HH.addr_of r1.ref =!= HH.addr_of r2.ref))
let lemma_distinct_addrs_distinct_mm #a #b #rel1 #rel2 m r1 r2 =
  Heap.lemma_distinct_addrs_distinct_mm (m `at` r1.id) (as_ref r1) (as_ref r2)

val sfree: #a:Type -> r:mmstackref a -> StackInline unit
  (requires (fun m0 -> r.id == m0.tip /\ m0 `contains` r))
  (ensures (fun m0 _ m1 -> m0 `contains` r /\ m1 == remove_reference r m0))
let sfree #a r =
  let m0 = gst_get () in
  let m1 = remove_reference r m0 in
  lemma_upd_tip_idempotent m0;
  assert (is_mm r) ;
  let aux (a:Type0) (rel:preorder a) (r0:mstackref a rel) : Lemma (requires (m0.h `HH.contains_ref` r0.ref /\ r0.id == r.id)) (ensures (HH.addr_of r0.ref =!= HH.addr_of r.ref)) =
    lemma_distinct_addrs_distinct_mm m0 r r0
  in
  FStar.Classical.(forall_intro_3 (fun a rel -> move_requires (aux a rel))) ;
  assert (forall (a:Type0) (rel:preorder a) (r:mreference a rel).
        m0 `contains` r /\ ref_requires r m1 ==> (m1 `contains` r /\ rel (sel m0 r) (sel m1 r))) ;
  assert (forall (i:HH.rid). Map.contains m0.h i ==> Map.contains m1.h i) ;
  assert (forall (i:HH.rid). ~(i `is_alive` m0) ==> ~(i `is_alive` m1)) ;
  assert (m0 `mem_rel` m1) ;
  gst_put m1

let fresh_region (r:HH.rid) (m0:mem) (m1:mem) =
  not (r `is_in` m0.h)
  /\ r `is_in` m1.h

(*
 * AR: using this in mitls code, so that it corresponds to the
 * fresh_region definition in hyperheap.
 *)
let stronger_fresh_region (r:HH.rid) (m0:mem) (m1:mem) =
   (forall j. HH.includes r j ==> not (j `is_in` m0.h))
   /\ r `is_in` m1.h

val new_region: r0:rid ->
  ST rid
    (requires (fun m -> is_eternal_region r0))
    (ensures (fun (m0:mem) (r1:rid) (m1:mem) ->
        r1 `HH.extends` r0
      /\ HH.fresh_region r1 m0.h m1.h
			/\ HH.color r1 == HH.color r0
			/\ m1.h == Map.upd m0.h r1 HH.emp
			/\ m1.tip == m0.tip
			))
let new_region r0 =
  (* TODO : We need some way to access the color of the region here *)
  (* if we really want/need to keep the same *)
  let c :c:int{c == HH.color r0} = admit () in
  fresh_child r0 c

let is_eternal_color = HS.is_eternal_color

val new_colored_region: r0:rid -> c:int -> ST rid
      (requires (fun m -> is_eternal_color c /\ is_eternal_region r0))
      (ensures (fun (m0:mem) (r1:rid) (m1:mem) ->
                           r1 `HH.extends` r0
                        /\ HH.fresh_region r1 m0.h m1.h
			/\ HH.color r1 == c
			/\ m1.h == Map.upd m0.h r1 HH.emp
			/\ m1.tip == m0.tip
			))
let new_colored_region r0 c =
  recall_weak_live_region r0 ;
  fresh_child r0 c

unfold let ralloc_post (#a:Type) (i:HH.rid) (init:a) (m0:mem) (x:reference a{is_eternal_region x.id}) (m1:mem) =
    let region_i = (Map.sel m0.h i).HH.m in
    (HH.as_ref x.ref) `Heap.unused_in` region_i
  /\ i `is_in` m0.h
  /\ i = x.id
  /\ m1 == upd m0 x init

private
val ralloc_maybe_mm: #a:Type -> i:rid -> init:a -> mm:bool -> ST (x:reference a{is_eternal_region x.id})
  (requires (fun m -> is_eternal_region i))
  (ensures (fun m0 x m1 -> ralloc_post i init m0 x m1 /\ is_mm x == mm))
let ralloc_maybe_mm #a i init mm =
  recall_weak_live_region i ;
  let m0 = gst_get () in
  let r, h = HH.alloc i (Heap.trivial_preorder a) m0.h init mm in
  HH.lemma_alloc i (Heap.trivial_preorder a) m0.h init mm ;
  lemma_upd_existing_rid_idempotent i m0;
  let m1 = HS h m0.tip in
  gst_put m1 ;
  let s = MkRef i r in
  gst_witness (valid_ref s) ;
  s

val ralloc: #a:Type -> i:rid -> init:a -> ST (ref a)
    (requires (fun m -> is_eternal_region i))
    (ensures (ralloc_post i init))
let ralloc #a i init = ralloc_maybe_mm #a i init false

val ralloc_mm: #a:Type -> i:rid -> init:a -> ST (mmref a)
    (requires (fun _ -> is_eternal_region i))
    (ensures (ralloc_post i init))
let ralloc_mm #a i init = ralloc_maybe_mm #a i init true

val rfree: #a:Type -> r:mmref a -> ST unit
  (requires (fun m0 -> m0 `contains` r))
  (ensures (fun m0 _ m1 -> m0 `contains` r /\ m1 == remove_reference r m0))
let rfree #a r =
  gst_recall (valid_ref r) ;
  let m0 = gst_get () in
  let m1 = remove_reference r m0 in
  lemma_upd_existing_rid_idempotent r.id m0;
  gst_put m1

unfold let assign_post (#a:Type) (r:reference a) (v:a) m0 (_u:unit) m1 =
  m0 `contains` r /\ m1 == HyperStack.upd m0 r v

(**
   Assigns, provided that the reference exists.
   Guaranties the strongest low-level effect: Stack
   *)
val op_Colon_Equals: #a:Type -> r:reference a -> v:a -> STL unit
  (requires (fun m -> m `contains` r))
  (ensures (assign_post r v))
let op_Colon_Equals #a r v =
  let m0 = gst_get () in
  let h1 = HH.upd_tot m0.h r.ref v in
  lemma_upd_existing_rid_idempotent r.id m0 ;
  let m1 = HS h1 m0.tip in
  gst_put m1

unfold let deref_post (#a:Type) (r:reference a) m0 x m1 =
  m1==m0 /\ x==HyperStack.sel m0 r

(**
   Dereferences, provided that the reference exists.
   Guaranties the strongest low-level effect: Stack
   *)
(*
 * AR: making the precondition as weak_contains.
 *)
val op_Bang: #a:Type -> r:reference a -> Stack a
  (requires (fun m -> m `weak_contains` r))
  (ensures (deref_post r))
let op_Bang #a r =
  let m0 = gst_get () in
  gst_recall (valid_ref r) ;
  HH.sel_tot m0.h r.ref

let modifies_none (h0:mem) (h1:mem) = modifies Set.empty h0 h1

module G = FStar.Ghost

//   NS: This version is just fine; all the operation on mem are ghost
//       and we can rig it so that mem just get erased at the end
(**
    Returns the current stack of heaps --- it should be erased
    *)
val get: unit -> Stack mem
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0==x /\ m1==m0))
let get () = gst_get ()

(**
   We can only recall refs with mm bit unset, not stack refs
   *)
val recall: #a:Type -> r:ref a -> Stack unit
  (requires (fun m -> True))
  (ensures (fun m0 _ m1 -> m0==m1 /\ m1 `contains` r))
let recall #a r = gst_recall (valid_ref r)

(**
   We can only recall eternal regions, not stack regions
   *)
val recall_region: i:rid{is_eternal_region i} -> Stack unit
  (requires (fun m -> True))
  (ensures (fun m0 _ m1 -> m0==m1 /\ i `is_in` m1.h))
let recall_region i = gst_recall (region_allocated_pred i)

val recall_region': i:rid -> Stack unit
  (requires (fun m -> weak_live_region m i))
  (ensures (fun m0 _ m1 -> m0==m1 /\ i `is_in` m1.h))
let recall_region' i = gst_recall (region_allocated_pred i)

(* Tests *)
val test_do_nothing: int -> Stack int
  (requires (fun h -> True))
  (ensures (fun h _ h1 -> True))
let test_do_nothing x =
  push_frame();
  pop_frame ();
  x

val test_do_something: s:stackref int -> Stack int
  (requires (fun h -> contains h s))
  (ensures (fun h r h1 -> contains h s /\ r = sel h s))
let test_do_something x =
  push_frame();
  let res = !x in
  pop_frame ();
  res

val test_do_something_else: s:stackref int -> v:int -> Stack unit
  (requires (fun h -> contains h s))
  (ensures (fun h r h1 -> contains h1 s /\ v = sel h1 s))
let test_do_something_else x v =
  push_frame();
  x := v;
  pop_frame ()

val test_allocate: unit -> Stack unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let test_allocate () =
  push_frame();
  let x = salloc 1 in
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
  let s = salloc x in
  s := (1 + x);
  pop_frame ();
  x

val test_stack_with_long_lived: s:reference int -> Stack unit
  (requires (fun h -> contains h s))
  (ensures  (fun h0 _ h1 -> contains h1 s /\ sel h1 s = (sel h0 s) + 1
    /\ modifies (Set.singleton s.id) h0 h1))
let test_stack_with_long_lived s =
  push_frame();
  let _ = test_stack !s in
  s := !s + 1;
  pop_frame()

val test_heap_code_with_stack_calls: unit -> Heap unit
  (requires (fun h -> heap_only h))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton h0.tip) h0 h1 ))
let test_heap_code_with_stack_calls () =
  let h = get () in
  // How is the following not known ?
  HH.root_has_color_zero ();
  (* TODO : the tip is always a valid rid, we should package that up *)
  gst_witness (region_allocated_pred h.tip) ;
  let s = ralloc h.tip 0 in
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
  gst_witness (region_allocated_pred h.tip) ;
  let new_region = new_colored_region h.tip color in
  let s = ralloc new_region 1 in
  test_stack_with_long_lived s; // STStack call
  test_heap_code_with_stack_calls (); // STHeap call
  ()

val test_lax_code_with_stack_calls_and_regions: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton HH.root) h0 h1 ))
let test_lax_code_with_stack_calls_and_regions () =
  push_frame();
  let color = 0 in
  HH.root_has_color_zero ();
  gst_witness (region_allocated_pred HH.root) ;
  let new_region = new_colored_region HH.root color in
  let s = ralloc new_region 1 in
  test_stack_with_long_lived s; // Stack call
  pop_frame()

val test_lax_code_with_stack_calls_and_regions_2: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton HH.root) h0 h1 ))
let test_lax_code_with_stack_calls_and_regions_2 () =
  push_frame();
  let color = 0 in
  HH.root_has_color_zero ();
  gst_witness (region_allocated_pred HH.root) ;
  let new_region = new_colored_region HH.root color in
  let s = ralloc new_region 1 in
  test_stack_with_long_lived s; // Stack call
  test_lax_code_with_stack_calls_and_regions (); // ST call
  pop_frame()

val test_to_be_stack_inlined: unit -> StackInline (reference int)
  (requires (fun h -> is_stack_region h.tip))
  (ensures  (fun h0 r h1 -> ~(contains h0 r) /\ contains h1 r /\ sel h1 r = 2))
let test_to_be_stack_inlined () =
  let r = salloc 0 in
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
  let r = salloc 0 in
  HH.root_has_color_zero ();
  gst_witness (region_allocated_pred HH.root) ;
  let region = new_region HH.root in
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

val with_frame: #a:Type -> #pre:gst_pre -> #post:(mem -> Tot (gst_post a)) -> $f:(unit -> Stack a pre post)
	     -> Stack a (fun s0 -> forall s1. fresh_frame s0 s1 ==> pre s1)
		     (fun s0 x s1 ->
			exists s0' s1'. fresh_frame s0 s0'
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
	     (ensures (fun m0 _ m1 -> modifies (Set.singleton x.id) m0 m1 /\ sel m1 x = v))
= let f _ : Stack unit (requires (fun m -> contains m x))
	      (ensures (fun m0 _ m1 -> modifies (Set.singleton x.id) m0 m1 /\ sel m1 x = v))
        = x := v
    in
  (* TODO : investigate why the lambda was not valid anymore *)
  with_frame f


let as_requires (#a:Type) (wp:gst_wp a) = wp (fun x s -> True)
let as_ensures (#a:Type) (wp:gst_wp a) = fun s0 x s1 -> wp (fun y s1' -> y=!=x \/ s1=!=s1') s0

(* assume val as_stack: #a:Type -> #wp:gst_wp a -> $f:(unit -> FStar.ST.STATE a wp) -> *)
(* 	   Pure (unit -> Stack a (as_requires wp) *)
(* 			      (as_ensures wp)) *)
(* 	        (requires (forall s0 x s1. as_ensures wp s0 x s1 ==> equal_domains s0 s1)) *)
(*  	        (ensures (fun x -> True)) *)

val mm_tests: unit -> Unsafe unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let mm_tests _ =
  let m0 = gst_get () in
  let _ = push_frame () in

  let r1 = salloc_mm 2 in

  //check that the heap contains the reference
  let m = get () in
  let h = m `at` m.tip in
  let _ = assert (Heap.contains h (HH.as_ref r1.ref)) in

  let _ = !r1 in

  let _ = sfree r1 in

  //this fails because the ref has been freed
  //let _ = !r1 in

  //check that the heap does not contain the reference
  let m = get () in
  let h = m `at` m.tip in
  let _ = assert (~ (Heap.contains h (HH.as_ref r1.ref))) in

  let r2 = salloc_mm 2 in
  let _ = pop_frame () in

  //this fails because the reference is no longer live
  //let _ = sfree r2 in
  gst_witness (region_allocated_pred HH.root) ;
  let id = new_region HH.root in

  let r3 = ralloc_mm id 2 in
  let _ = !r3 in
  let _ = rfree r3 in

  //check that the heap does not contain the reference
  let m = get () in
  let h = m `at` id in
  let _ = assert (~ (Heap.contains h (HH.as_ref r3.ref))) in

  //this fails because the reference is no longer live
  //let _ = !r3 in

  //this fails because recall of mm refs is not allowed
  //let _ = recall r3 in
  ()
