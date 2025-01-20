(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.HyperStack.ST

open FStar.HyperStack

module HS = FStar.HyperStack

open FStar.Preorder

(* Setting up the preorder for mem *)

(* Starting the predicates that constitute the preorder *)

[@@"opaque_to_smt"]
private unfold let contains_region (m:mem) (r:rid) = get_hmap m `Map.contains` r

(* The preorder is the conjunction of above predicates *)
val mem_rel :preorder mem

type mem_predicate = mem -> Type0

(* Predicates that we will witness with regions and refs *)
val region_contains_pred (r:HS.rid) :mem_predicate

val ref_contains_pred (#a:Type) (#rel:preorder a) (r:HS.mreference a rel) :mem_predicate

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
 *     - `lemma_functoriality` does not require stability for either `p` or `q`
 *       Our metatheory ensures that this is sound (without requiring stability of `q`)
 *       This form is useful in defining the MRRef interface (see mr_witness)
 *)
       
val stable (p:mem_predicate) :Type0

val witnessed (p:mem_predicate) :Type0

(* TODO: we should derive these using DM4F *)
private val gst_get: unit    -> GST mem (fun p h0 -> p h0 h0)
private val gst_put: h1:mem -> GST unit (fun p h0 -> mem_rel h0 h1 /\ p () h1)

private val gst_witness: p:mem_predicate -> GST unit (fun post h0 -> p h0 /\ stable p /\ (witnessed p ==> post () h0))
private val gst_recall:  p:mem_predicate -> GST unit (fun post h0 -> witnessed p /\ (p h0 ==> post () h0))

val lemma_functoriality (p:mem_predicate{witnessed p}) (q:mem_predicate{(forall (h:mem). p h ==> q h)})
  : Lemma (witnessed q)

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
[@@"opaque_to_smt"]
unfold private let equal_heap_dom (r:rid) (m0 m1:mem) :Type0
  = Heap.equal_dom (get_hmap m0 `Map.sel` r) (get_hmap m1 `Map.sel` r)

[@@"opaque_to_smt"]
unfold private let contained_region :mem -> mem -> rid -> Type0
  = fun m0 m1 r -> m0 `contains_region` r /\ m1 `contains_region` r

[@@"opaque_to_smt"]
unfold private let contained_stack_region :mem -> mem -> rid -> Type0
  = fun m0 m1 r -> is_stack_region r /\ contained_region m0 m1 r

[@@"opaque_to_smt"]
unfold private let contained_non_tip_region :mem -> mem -> rid -> Type0
  = fun m0 m1 r -> r =!= get_tip m0 /\ r =!= get_tip m1 /\ contained_region m0 m1 r

[@@"opaque_to_smt"]
unfold private let contained_non_tip_stack_region :mem -> mem -> rid -> Type0
  = fun m0 m1 r -> is_stack_region r /\ contained_non_tip_region m0 m1 r

[@@"opaque_to_smt"]
unfold private let same_refs_common (p:mem -> mem -> rid -> Type0) (m0 m1:mem) =
  forall (r:rid). p m0 m1 r ==> equal_heap_dom r m0 m1

(* predicates *)
val same_refs_in_all_regions (m0 m1:mem) :Type0
val same_refs_in_stack_regions (m0 m1:mem) :Type0
val same_refs_in_non_tip_regions (m0 m1:mem) :Type0
val same_refs_in_non_tip_stack_regions (m0 m1:mem) :Type0

(* intro and elim forms *)
val lemma_same_refs_in_all_regions_intro (m0 m1:mem)
  :Lemma (requires (same_refs_common contained_region m0 m1)) (ensures  (same_refs_in_all_regions m0 m1))
	 [SMTPat (same_refs_in_all_regions m0 m1)]
val lemma_same_refs_in_all_regions_elim (m0 m1:mem) (r:rid)
  :Lemma (requires (same_refs_in_all_regions m0 m1 /\ contained_region m0 m1 r)) (ensures  (equal_heap_dom r m0 m1))
	 [SMTPatOr [[SMTPat (same_refs_in_all_regions m0 m1); SMTPat (m0 `contains_region` r)];
                    [SMTPat (same_refs_in_all_regions m0 m1); SMTPat (m1 `contains_region` r)]]]

val lemma_same_refs_in_stack_regions_intro (m0 m1:mem)
  :Lemma (requires (same_refs_common contained_stack_region m0 m1)) (ensures  (same_refs_in_stack_regions m0 m1))
	 [SMTPat  (same_refs_in_stack_regions m0 m1)]
val lemma_same_refs_in_stack_regions_elim (m0 m1:mem) (r:rid)
  :Lemma (requires (same_refs_in_stack_regions m0 m1 /\ contained_stack_region m0 m1 r)) (ensures  (equal_heap_dom r m0 m1))
	 [SMTPatOr [[SMTPat (same_refs_in_stack_regions m0 m1); SMTPat (is_stack_region r); SMTPat (m0 `contains_region` r)];
                    [SMTPat (same_refs_in_stack_regions m0 m1); SMTPat (is_stack_region r); SMTPat (m1 `contains_region` r)]]]

val lemma_same_refs_in_non_tip_regions_intro (m0 m1:mem)
  :Lemma (requires (same_refs_common contained_non_tip_region m0 m1)) (ensures (same_refs_in_non_tip_regions m0 m1))
         [SMTPat (same_refs_in_non_tip_regions m0 m1)]

val lemma_same_refs_in_non_tip_regions_elim (m0 m1:mem) (r:rid)
  :Lemma (requires (same_refs_in_non_tip_regions m0 m1 /\ contained_non_tip_region m0 m1 r)) (ensures  (equal_heap_dom r m0 m1))
	 [SMTPatOr [[SMTPat (same_refs_in_non_tip_regions m0 m1); SMTPat (m0 `contains_region` r)];
                    [SMTPat (same_refs_in_non_tip_regions m0 m1); SMTPat (m1 `contains_region` r)]]]

val lemma_same_refs_in_non_tip_stack_regions_intro (m0 m1:mem)
  :Lemma (requires (same_refs_common contained_non_tip_stack_region m0 m1)) (ensures (same_refs_in_non_tip_stack_regions m0 m1))
         [SMTPat (same_refs_in_non_tip_stack_regions m0 m1)]
val lemma_same_refs_in_non_tip_stack_regions_elim (m0 m1:mem) (r:rid)
  :Lemma (requires (same_refs_in_non_tip_stack_regions m0 m1 /\ contained_non_tip_stack_region m0 m1 r))
         (ensures  (equal_heap_dom r m0 m1))
	 [SMTPatOr [[SMTPat (same_refs_in_non_tip_stack_regions m0 m1); SMTPat (is_stack_region r); SMTPat (m0 `contains_region` r);];
                    [SMTPat (same_refs_in_non_tip_stack_regions m0 m1); SMTPat (is_stack_region r); SMTPat (m1 `contains_region` r)]]]

(******)

let equal_domains (m0 m1:mem) =
  get_tip m0 == get_tip m1 /\
  Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)) /\
  same_refs_in_all_regions m0 m1

val lemma_equal_domains_trans (m0 m1 m2:mem)
  :Lemma (requires (equal_domains m0 m1 /\ equal_domains m1 m2))
         (ensures  (equal_domains m0 m2))
         [SMTPat (equal_domains m0 m1); SMTPat (equal_domains m1 m2)]

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
 * Effect that indicates to the Karamel compiler that allocation may occur in the caller's frame.
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
 * Effect that indicates to the Karamel compiler that allocation may occur in the caller's frame.
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
  = HS.is_eternal_region_hs r /\ (r == HS.root \/ witnessed (region_contains_pred r))

(*
 * AR: The change to using ST.rid may not be that bad itself,
 *     since subtyping should take care of most instances in the client usage.
 *     However, one case where it could be an issue is modifies clauses that use
 *     Set.set rid.
 *)

(** Pushes a new empty frame on the stack **)
val push_frame (_:unit) :Unsafe unit (requires (fun m -> True)) (ensures (fun (m0:mem) _ (m1:mem) -> fresh_frame m0 m1))

(** Removes old frame from the stack **)
val pop_frame (_:unit)
  :Unsafe unit (requires (fun m -> poppable m))
               (ensures (fun (m0:mem) _ (m1:mem) -> poppable m0 /\ m1 == pop m0 /\ popped m0 m1))

#push-options "--z3rlimit 40"
let salloc_post (#a:Type) (#rel:preorder a) (init:a) (m0:mem)
                (s:mreference a rel{is_stack_region (frameOf s)}) (m1:mem)
  = is_stack_region (get_tip m0)                          /\
    Map.domain (get_hmap m0) == Map.domain (get_hmap m1)  /\
    get_tip m0 == get_tip m1                              /\
    frameOf s   = get_tip m1                              /\
    HS.fresh_ref s m0 m1                                  /\  //it's a fresh reference in the top frame
    m1 == HyperStack.upd m0 s init  //and it's been initialized
#pop-options

(**
 * Allocates on the top-most stack frame
 *)
val salloc (#a:Type) (#rel:preorder a) (init:a)
  :StackInline (mstackref a rel) (requires (fun m -> is_stack_region (get_tip m)))
                                 (ensures  salloc_post init)
  
// JP, AR: these are not supported in C, and `salloc` already benefits from
// automatic memory management.
[@@ (deprecated "Use salloc instead") ]
val salloc_mm (#a:Type) (#rel:preorder a) (init:a)
  :StackInline (mmmstackref a rel) (requires (fun m -> is_stack_region (get_tip m)))
                                   (ensures  salloc_post init)

[@@ (deprecated "Use salloc instead") ]
val sfree (#a:Type) (#rel:preorder a) (r:mmmstackref a rel)
  :StackInline unit (requires (fun m0 -> frameOf r = get_tip m0 /\ m0 `contains` r))
                    (ensures (fun m0 _ m1 -> m0 `contains` r /\ m1 == HS.free r m0))

unfold
let new_region_post_common (r0 r1:rid) (m0 m1:mem) =
  r1 `HS.extends` r0 /\
  HS.fresh_region r1 m0 m1 /\
  get_hmap m1 == Map.upd (get_hmap m0) r1 Heap.emp /\
  get_tip m1 == get_tip m0 /\ 
  HS.live_region m0 r0

val new_region (r0:rid)
  :ST rid
      (requires (fun m        -> is_eternal_region r0))
      (ensures  (fun m0 r1 m1 ->
                 new_region_post_common r0 r1 m0 m1               /\
		 HS.color r1 = HS.color r0                        /\
		 is_eternal_region r1                             /\
                 (r1, m1) == HS.new_eternal_region m0 r0 None))

val new_colored_region (r0:rid) (c:int)
  :ST rid
      (requires (fun m       -> HS.is_heap_color c /\ is_eternal_region r0))
      (ensures (fun m0 r1 m1 ->
                new_region_post_common r0 r1 m0 m1               /\
	        HS.color r1 = c                                  /\
		is_eternal_region r1                             /\
                (r1, m1) == HS.new_eternal_region m0 r0 (Some c)))

let ralloc_post (#a:Type) (#rel:preorder a) (i:rid) (init:a) (m0:mem)
                       (x:mreference a rel) (m1:mem) =
  let region_i = get_hmap m0 `Map.sel` i in
  as_ref x `Heap.unused_in` region_i /\
  i `is_in` get_hmap m0              /\
  i = frameOf x                      /\
  m1 == upd m0 x init                      

val ralloc (#a:Type) (#rel:preorder a) (i:rid) (init:a)
  :ST (mref a rel) (requires (fun m -> is_eternal_region i))
                   (ensures  (ralloc_post i init))
  
val ralloc_mm (#a:Type) (#rel:preorder a) (i:rid) (init:a)
  :ST (mmmref a rel) (requires (fun m -> is_eternal_region i))
                     (ensures  (ralloc_post i init))

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

val rfree (#a:Type) (#rel:preorder a) (r:mreference a rel{HS.is_mm r /\ HS.is_heap_color (HS.color (HS.frameOf r))})
  :ST unit (requires (fun m0     -> r `is_live_for_rw_in` m0))
           (ensures (fun m0 _ m1 -> m0 `contains` r /\ m1 == HS.free r m0))

unfold let assign_post (#a:Type) (#rel:preorder a) (r:mreference a rel) (v:a) (m0:mem) (_:unit) (m1:mem) =
  m0 `contains` r /\ m1 == HyperStack.upd m0 r v

(**
 * Assigns, provided that the reference exists.
 * Guarantees the strongest low-level effect: Stack
 *)
val op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mreference a rel) (v:a)
  :STL unit (requires (fun m -> r `is_live_for_rw_in` m /\ rel (HS.sel m r) v))
            (ensures  (assign_post r v))

unfold let deref_post (#a:Type) (#rel:preorder a) (r:mreference a rel) (m0:mem) (x:a) (m1:mem) =
  m1 == m0 /\ m0 `contains` r /\ x == HyperStack.sel m0 r

(**
 * Dereferences, provided that the reference exists.
 * Guarantees the strongest low-level effect: Stack
 *)
val op_Bang (#a:Type) (#rel:preorder a) (r:mreference a rel)
  :Stack a (requires (fun m -> r `is_live_for_rw_in` m))
           (ensures  (deref_post r))

let modifies_none (h0:mem) (h1:mem) = modifies Set.empty h0 h1

//   NS: This version is just fine; all the operation on mem are ghost
//       and we can rig it so that mem just get erased at the end
(**
 * Returns the current stack of heaps --- it should be erased
 *)
val get (_:unit)
  :Stack mem (requires (fun m -> True))
             (ensures (fun m0 x m1 -> m0 == x /\ m1 == m0))

(**
 * We can only recall refs with mm bit unset, not stack refs
 *)
val recall (#a:Type) (#rel:preorder a) (r:mreference a rel{not (HS.is_mm r)})
  :Stack unit (requires (fun m -> is_eternal_region (HS.frameOf r) \/ m `contains_region` (HS.frameOf r)))
              (ensures  (fun m0 _ m1 -> m0 == m1 /\ m1 `contains` r))

(**
 * We can only recall eternal regions, not stack regions
 *)
val recall_region (i:rid{is_eternal_region i})
  :Stack unit (requires (fun m -> True))
              (ensures (fun m0 _ m1 -> m0 == m1 /\ i `is_in` get_hmap m1))

val witness_region (i:rid)
  :Stack unit (requires (fun m0      -> HS.is_eternal_region_hs i ==> i `is_in` get_hmap m0))
              (ensures  (fun m0 _ m1 -> m0 == m1 /\ witnessed (region_contains_pred i)))

val witness_hsref (#a:Type) (#rel:preorder a) (r:HS.mreference a rel)
  :ST unit (fun h0      -> h0 `HS.contains` r)
           (fun h0 _ h1 -> h0 == h1 /\ witnessed (ref_contains_pred r))

(** MR witness etc. **)

type erid = r:rid{is_eternal_region r}

type m_rref (r:erid) (a:Type) (b:preorder a) = x:mref a b{HS.frameOf x = r}

(* states that p is preserved by any valid updates on r; note that h0 and h1 may differ arbitrarily elsewhere, hence proving stability usually requires that p depends only on r's content. 
 *)
unfold type stable_on (#a:Type0) (#rel:preorder a) (p:mem_predicate) (r:mreference a rel)
  = forall (h0 h1:mem).{:pattern (p h0); rel (HS.sel h0 r) (HS.sel h1 r)}
                  (p h0 /\ rel (HS.sel h0 r) (HS.sel h1 r)) ==> p h1

(*
 * The stable_on_t and mr_witness API is here for legacy reasons,
 * the preferred API is stable_on and witness_p
 *)

unfold type stable_on_t (#i:erid) (#a:Type) (#b:preorder a)
                        (r:m_rref i a b) (p:mem_predicate)
  = stable_on p r

val mr_witness (#r:erid) (#a:Type) (#b:preorder a)
               (m:m_rref r a b) (p:mem_predicate)
  :ST unit (requires (fun h0      -> p h0   /\ stable_on_t m p))
           (ensures  (fun h0 _ h1 -> h0==h1 /\ witnessed p))

val weaken_witness (p q:mem_predicate)
  :Lemma ((forall h. p h ==> q h) /\ witnessed p ==> witnessed q)

val testify (p:mem_predicate)
  :ST unit (requires (fun _      ->  witnessed p))
           (ensures (fun h0 _ h1 -> h0==h1 /\ p h1))

val testify_forall (#c:Type) (#p:(c -> mem -> Type0))
  ($s:squash (forall (x:c). witnessed (p x)))
  :ST unit (requires (fun h      -> True))
           (ensures (fun h0 _ h1 -> h0==h1 /\ (forall (x:c). p x h1)))

val testify_forall_region_contains_pred (#c:Type) (#p:(c -> GTot rid))
  ($s:squash (forall (x:c). witnessed (region_contains_pred (p x))))
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\
	                          (forall (x:c). HS.is_eternal_region_hs (p x) ==> h1 `contains_region` (p x))))


(****** Begin: preferred API for witnessing and recalling predicates ******)


val token_p (#a:Type0) (#rel:preorder a) (r:mreference a rel) (p:mem_predicate) :Type0

val witness_p (#a:Type0) (#rel:preorder a) (r:mreference a rel) (p:mem_predicate)
  :ST unit (fun h0      -> p h0 /\ p `stable_on` r)
           (fun h0 _ h1 -> h0 == h1 /\ token_p r p)

val recall_p (#a:Type0) (#rel:preorder a) (r:mreference a rel) (p:mem_predicate)
  :ST unit (fun h0      -> ((is_eternal_region (HS.frameOf r) /\ not (HS.is_mm r)) \/ h0 `HS.contains` r) /\ token_p r p)
           (fun h0 _ h1 -> h0 == h1 /\ h0 `HS.contains` r /\ p h0)

val token_functoriality
  (#a:Type0) (#rel:preorder a) (r:mreference a rel)
  (p:mem_predicate{token_p r p}) (q:mem_predicate{forall (h:mem). p h ==> q h})
  : Lemma (token_p r q)


(****** End: preferred API for witnessing and recalling predicates ******)


type ex_rid = erid


(****** logical properties of witnessed ******)

val lemma_witnessed_constant (p:Type0)
  :Lemma (witnessed (fun (m:mem) -> p) <==> p)

val lemma_witnessed_nested (p:mem_predicate)
  : Lemma (witnessed (fun (m:mem) -> witnessed p) <==> witnessed p)

val lemma_witnessed_and (p q:mem_predicate)
  :Lemma (witnessed (fun s -> p s /\ q s) <==> (witnessed p /\ witnessed q))

val lemma_witnessed_or (p q:mem_predicate)
  :Lemma ((witnessed p \/ witnessed q) ==> witnessed (fun s -> p s \/ q s))

val lemma_witnessed_impl (p q:mem_predicate)
  :Lemma ((witnessed (fun s -> p s ==> q s) /\ witnessed p) ==> witnessed q)

val lemma_witnessed_forall (#t:Type) (p:(t -> mem_predicate))
  :Lemma ((witnessed (fun s -> forall x. p x s)) <==> (forall x. witnessed (p x)))

val lemma_witnessed_exists (#t:Type) (p:(t -> mem_predicate))
  :Lemma ((exists x. witnessed (p x)) ==> witnessed (fun s -> exists x. p x s))


(*** Support for dynamic regions ***)


let is_freeable_heap_region (r:rid) : Type0 =
  HS.is_heap_color (color r) /\ HS.rid_freeable r /\ witnessed (region_contains_pred r)

type d_hrid = r:rid{is_freeable_heap_region r}

val drgn : Type0

val rid_of_drgn (d:drgn) : d_hrid

val new_drgn (r0:rid)
: ST drgn
  (requires fun m -> is_eternal_region r0)
  (ensures fun m0 d m1 ->
    let r1 = rid_of_drgn d in
    new_region_post_common r0 r1 m0 m1 /\
    HS.color r1 == HS.color r0 /\
    (r1, m1) == HS.new_freeable_heap_region m0 r0)

val free_drgn (d:drgn)
: ST unit
  (requires fun m -> contains_region m (rid_of_drgn d))
  (ensures fun m0 _ m1 -> m1 == HS.free_heap_region m0 (rid_of_drgn d))

val ralloc_drgn (#a:Type) (#rel:preorder a) (d:drgn) (init:a)
: ST (mreference a rel)
  (requires fun m -> m `contains_region` (rid_of_drgn d))
  (ensures fun m0 r m1 ->
    not (HS.is_mm r) /\
    ralloc_post (rid_of_drgn d) init m0 r m1)

val ralloc_drgn_mm (#a:Type) (#rel:preorder a) (d:drgn) (init:a)
: ST (mreference a rel)
  (requires fun m -> m `contains_region` (rid_of_drgn d))
  (ensures fun m0 r m1 ->
    HS.is_mm r /\
    ralloc_post (rid_of_drgn d) init m0 r m1)


(* This causes the verification conditition for the continuation
of the call to this function to be done in a separate Z3 query. *)
inline_for_extraction
let break_vc ()
  : STATE unit (fun p h -> spinoff (squash (p () h)))
  = ()
