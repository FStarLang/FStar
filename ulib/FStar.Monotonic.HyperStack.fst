module FStar.Monotonic.HyperStack

open FStar.Preorder
module Map = FStar.Map

include FStar.Monotonic.HyperHeap

unfold let is_in (r:rid) (h:hmap) = h `Map.contains` r

let is_stack_region r = color r > 0
let is_eternal_color c = c <= 0
let is_eternal_region r  = is_eternal_color (color r)

type sid = r:rid{is_stack_region r} //stack region ids

(*
 * AR: marking these unfolds, else I think there are pattern firing issues depending on which one we use
 *)
unfold let is_above r1 r2          = r1 `includes` r2
unfold let is_just_below r1 r2     = r1 `extends`  r2
unfold let is_below r1 r2          = r2 `is_above` r1
let is_strictly_below r1 r2 = r1 `is_below` r2 && r1 <> r2
let is_strictly_above r1 r2 = r1 `is_above` r2 && r1 <> r2

//All regions above a contained region are contained
abstract let map_invariant (m:hmap) =
  forall r. Map.contains m r ==>
      (forall s. includes s r ==> Map.contains m s)

abstract let downward_closed (h:hmap) =
  forall (r:rid). r `is_in` h  //for any region in the memory
        ==> (r=root    //either is the root
            \/ (forall (s:rid). r `is_above` s  //or, any region beneath it
                          /\ s `is_in` h   //that is also in the memory
                     ==> (is_stack_region r = is_stack_region s))) //must be of the same flavor as itself

abstract let tip_top (tip:rid) (h:hmap) =
  forall (r:sid). r `is_in` h <==> r `is_above` tip

let is_tip (tip:rid) (h:hmap) =
  (is_stack_region tip \/ tip = root) /\  //the tip is a stack region, or the root
  tip `is_in` h                      /\   //the tip is live
  tip_top tip h                          //any other sid activation is a above (or equal to) the tip

let rid_last_component (r:rid) :GTot int
  = let open FStar.List.Tot in
    let r = reveal r in
    if length r = 0 then 0
    else snd (hd r)

(*
 * AR: all live regions have last component less than the rid_ctr
 *     marking it abstract, else it has a high-chance of firing even with a pattern
 *)
abstract let rid_ctr_pred (h:hmap) (n:int) =
  forall (r:rid).{:pattern (h `Map.contains` r)}
               h `Map.contains` r ==> rid_last_component r < n

let is_wf_with_ctr_and_tip (h:hmap) (ctr:int) (tip:rid) :Type0
  = root `is_in` h /\ tip `is_tip` h /\ map_invariant h /\ downward_closed h /\ rid_ctr_pred h ctr
  
noeq type mem =
  | HS : rid_ctr:int
         -> h:hmap
         -> tip:rid{is_wf_with_ctr_and_tip h rid_ctr tip}
         -> mem

(******* map_invariant related lemmas ******)

let lemma_map_invariant (m:mem) (r s:rid)
  :Lemma (requires (r `is_in` m.h /\ s `is_above` r))
         (ensures  (s `is_in` m.h))
         [SMTPat (r `is_in` m.h); SMTPat (s `is_above` r); SMTPat (s `is_in` m.h)]
  = ()

(******)


(****** downward_closed related lemmas *******)

let lemma_downward_closed (m:mem) (r:rid) (s:rid{s =!= root})
  :Lemma (requires (r `is_in` m.h /\ s `is_above` r))
         (ensures  (is_eternal_region r == is_eternal_region s /\ is_stack_region r == is_stack_region s))
         [SMTPatOr [[SMTPat (m.h `Map.contains` r); SMTPat (s `is_above` r); SMTPat (is_eternal_region s)];
                    [SMTPat (m.h `Map.contains` r); SMTPat (s `is_above` r); SMTPat (is_stack_region s)]
                    ]]
  = ()

(******)

(****** tip_top related lemmas ******)

let lemma_tip_top (m:mem) (r:sid)
  :Lemma (r `is_in` m.h <==> r `is_above` m.tip)
  = ()

(*
 * Pointer uses lemma_tip_top by calling it explicitly with Classical.forall_intro2
 * Classical.forall_intro2 does not work well with SMTPat
 * So adding this smt form of the same lemma
 *)
let lemma_tip_top_smt (m:mem) (r:rid)
  :Lemma (requires (is_stack_region r))
         (ensures  (r `is_in` m.h <==> r `is_above` m.tip))
         [SMTPatOr [[SMTPat (is_stack_region r); SMTPat (r `is_above` m.tip)];
                    [SMTPat (is_stack_region r); SMTPat (r `is_in` m.h)]]]
  = ()

(******)

(****** rid_ctr_pred related lemmas ******)

(*
 * Expose the meaning of the predicate itself
 *)
let lemma_rid_ctr_pred ()
  :Lemma (forall (m:mem) (r:rid).{:pattern (m.h `Map.contains` r)} m.h `Map.contains` r ==> rid_last_component r < m.rid_ctr)
  = ()

(*****)

let empty_mem (m:hmap) =
  let empty_map = Map.restrict (Set.empty) m in
  let h = Map.upd empty_map root Heap.emp in
  let tip = root in
  assume (rid_last_component root == 0);
  HS 1 h tip

let eternal_region_does_not_overlap_with_tip (m:mem) (r:rid{is_eternal_region r /\ not (disjoint r m.tip) /\ r<>root /\ is_stack_region m.tip})
  : Lemma (requires True)
          (ensures (~ (r `is_in` m.h)))
  = root_has_color_zero()

let poppable m = m.tip <> root

let remove_elt (#a:eqtype) (s:Set.set a) (x:a) = Set.intersect s (Set.complement (Set.singleton x))

let popped m0 m1 =
  poppable m0
  /\ parent m0.tip = m1.tip
  /\ Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip)
  /\ Map.equal m1.h (Map.restrict (Map.domain m1.h) m0.h)

let pop (m0:mem{poppable m0}) : Tot mem =
  root_has_color_zero();
  let dom = remove_elt (Map.domain m0.h) m0.tip in
  let h0 = m0.h in
  let h1 = Map.restrict dom m0.h in
  let tip0 = m0.tip in
  let tip1 = parent tip0 in
  HS m0.rid_ctr h1 tip1

//A (reference a) may reside in the stack or heap, and may be manually managed
//Mark it private so that clients can't use its projectors etc.
//enabling extraction of mreference to just a reference in ML and pointer in C
//note that this not enforcing any abstraction
(*
 * AR: 12/26: Defining it using Heap.mref directly, removing the HyperHeap.mref indirection
 *)
private
noeq
type mreference' (a:Type) (rel:preorder a) =
  | MkRef : frame:rid -> ref:Heap.mref a rel -> mreference' a rel

let mreference a rel = mreference' a rel

//TODO: rename to frame_of, avoiding the inconsistent use of camelCase
let frameOf (#a:Type) (#rel:preorder a) (r:mreference a rel)
  : Tot rid
  = r.frame

let mk_mreference (#a:Type) (#rel:preorder a) (id:rid)
                  (r:Heap.mref a rel)
  : Tot (mreference a rel)
  = MkRef id r

//Hopefully we can get rid of this one
abstract let as_ref #a #rel (x:mreference a rel)
  : Tot (Heap.mref a rel)
  = MkRef?.ref x

//And make this one abstract
let as_addr #a #rel (x:mreference a rel)
  : GTot nat
  = Heap.addr_of (as_ref x)

let lemma_as_ref_inj (#a:Type) (#rel:preorder a) (r:mreference a rel)
  :Lemma (requires True) (ensures (mk_mreference (frameOf r) (as_ref r) == r))
         [SMTPat (as_ref r)]
  = ()

let is_mm (#a:Type) (#rel:preorder a) (r:mreference a rel) :GTot bool =
  Heap.is_mm (as_ref r)

// Warning: all of the type aliases below get special support for KreMLin
// extraction. If you rename or add to this list,
// src/extraction/FStar.Extraction.Kremlin.fs needs to be updated.

//adding (not s.mm) to stackref and ref so as to keep their semantics as is
let mstackref (a:Type) (rel:preorder a) =
  s:mreference a rel{ is_stack_region (frameOf s)  && not (is_mm s) }

let mref (a:Type) (rel:preorder a) =
  s:mreference a rel{ is_eternal_region (frameOf s) && not (is_mm s) }

let mmmstackref (a:Type) (rel:preorder a) =
  s:mreference a rel{ is_stack_region (frameOf s) && is_mm s }

let mmmref (a:Type) (rel:preorder a) =
  s:mreference a rel{ is_eternal_region (frameOf s) && is_mm s }

//NS: Why do we need this one?
let s_mref (i:rid) (a:Type) (rel:preorder a) = s:mreference a rel{frameOf s = i}

(*
 * AR: this used to be (is_eternal_region i \/ i `is_above` m.tip) /\ Map.contains ...
 *     As far as the memory model is concerned, this should just be Map.contains
 *     The fact that an eternal region is always contained (because of monotonicity) should be used in the ST interface
 *)
let live_region (m:mem) (i:rid) :Tot bool = Map.contains m.h i

let contains (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel) :GTot bool =
  let i = frameOf s in
  live_region m i && (FStar.StrongExcludedMiddle.strong_excluded_middle (Heap.contains (Map.sel m.h i) (as_ref s)))

let unused_in (#a:Type) (#rel:preorder a) (r:mreference a rel) (h:mem) :GTot bool =
  let i = frameOf r in
  not (Map.contains h.h i) ||
  FStar.StrongExcludedMiddle.strong_excluded_middle (Heap.unused_in (as_ref r) (Map.sel h.h i))

let contains_ref_in_its_region (#a:Type) (#rel:preorder a) (h:mem) (r:mreference a rel) :GTot bool =
  let i = frameOf r in
  FStar.StrongExcludedMiddle.strong_excluded_middle (Heap.contains (Map.sel h.h i) (as_ref r))

let fresh_ref (#a:Type) (#rel:preorder a) (r:mreference a rel) (m0:mem) (m1:mem) :Type0 =
  let i = frameOf r in
  Heap.fresh (as_ref r) (Map.sel m0.h i) (Map.sel m1.h i)

let fresh_region (i:rid) (m0 m1:mem) =
  not (m0.h `Map.contains` i) /\ m1.h `Map.contains` i

abstract val lemma_extends_fresh_disjoint: i:rid -> j:rid -> ipar:rid -> jpar:rid
                               -> m0:mem{map_invariant m0.h} -> m1:mem{map_invariant m1.h} ->
  Lemma (requires (fresh_region i m0 m1
                  /\ fresh_region j m0 m1
                  /\ Map.contains m0.h ipar
                  /\ Map.contains m0.h jpar
                  /\ extends i ipar
                  /\ extends j jpar
                  /\ i<>j))
        (ensures (disjoint i j))
        [SMTPat (fresh_region i m0 m1);
         SMTPat (fresh_region j m0 m1);
         SMTPat (extends i ipar);
         SMTPat (extends j jpar)]
let lemma_extends_fresh_disjoint i j ipar jpar m0 m1 = ()

(*
 * memory model API
 *)
let sel (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel)
  : GTot a
  = Heap.sel (Map.sel m.h (frameOf s)) (as_ref s)

let upd (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel{live_region m (frameOf s)}) (v:a)
  : GTot mem
  = let i = frameOf s in
    HS m.rid_ctr (Map.upd m.h i (Heap.upd (Map.sel m.h i) (as_ref s) v)) m.tip

let alloc (#a:Type0) (rel:preorder a) (id:rid) (init:a) (mm:bool) (m:mem{m.h `Map.contains` id})
  :Tot (p:(mreference a rel * mem){let (r, h) = Heap.alloc rel (Map.sel m.h id) init mm in
                                   as_ref (fst p) == r /\
                                   (snd p).h == Map.upd m.h id h})
  = let r, h = Heap.alloc rel (Map.sel m.h id) init mm in
    (mk_mreference id r), (HS m.rid_ctr (Map.upd m.h id h) m.tip)

let free (#a:Type0) (#rel:preorder a) (r:mreference a rel{is_mm r}) (m:mem{m `contains` r})
  :Tot mem
  = let i = frameOf r in
    let h = Map.sel m.h i in
    let new_h = Heap.free_mm h (as_ref r) in
    HS m.rid_ctr (Map.upd m.h i new_h) m.tip

let upd_tot (#a:Type) (#rel:preorder a) (m:mem) (r:mreference a rel{m `contains` r}) (v:a)
  :Tot mem
  = let i = frameOf r in
    let h = Map.sel m.h i in
    let new_h = Heap.upd_tot h (as_ref r) v in
    HS m.rid_ctr (Map.upd m.h i new_h) m.tip

let sel_tot (#a:Type) (#rel:preorder a) (m:mem) (r:mreference a rel{m `contains` r})
  :Tot a
  = Heap.sel_tot (Map.sel m.h (frameOf r)) (as_ref r)

let fresh_frame (m0:mem) (m1:mem) =
  not (Map.contains m0.h m1.tip) /\
  parent m1.tip = m0.tip         /\
  m1.h == Map.upd m0.h m1.tip Heap.emp

let hs_push_frame (m:mem) :Tot (m':mem{fresh_frame m m'})
  = let new_tip_rid = extend m.tip m.rid_ctr 1 in
    HS (m.rid_ctr + 1) (Map.upd m.h new_tip_rid Heap.emp) new_tip_rid

let new_eternal_region (m:mem) (parent:rid{is_eternal_region parent /\ m.h `Map.contains` parent})
                       (c:option int{None? c \/ is_eternal_color (Some?.v c)})
  :Tot (t:(rid * mem){fresh_region (fst t) m (snd t)})
  = let new_rid =
      if None? c then extend_monochrome parent m.rid_ctr
      else extend parent m.rid_ctr (Some?.v c)
    in
    let h1 = Map.upd m.h new_rid Heap.emp in
    new_rid, HS (m.rid_ctr + 1) h1 m.tip

(****** The following two lemmas are only used in FStar.Pointer.Base, and invoked explicitly ******)

let lemma_sel_same_addr (#a:Type0) (#rel:preorder a) (h:mem) (r1:mreference a rel) (r2:mreference a rel)
  :Lemma (requires (frameOf r1 == frameOf r2 /\ h `contains` r1 /\ as_addr r1 = as_addr r2 /\ is_mm r1 == is_mm r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
  = Heap.lemma_sel_same_addr (Map.sel h.h (frameOf r1)) (as_ref r1) (as_ref r2)

let lemma_upd_same_addr (#a:Type0) (#rel:preorder a) (h:mem) (r1 r2:mreference a rel) (x: a)
  :Lemma (requires (frameOf r1 == frameOf r2 /\ (h `contains` r1 \/ h `contains` r2) /\
                    as_addr r1 == as_addr r2 /\ is_mm r1 == is_mm r2))
         (ensures  (h `contains` r1 /\ h `contains` r2 /\ upd h r1 x == upd h r2 x))
  = if StrongExcludedMiddle.strong_excluded_middle (h `contains` r1) then
      lemma_sel_same_addr h r1 r2
    else lemma_sel_same_addr h r2 r1

(*
 * AR: 12/26: modifies clauses
 *            NOTE: the modifies clauses used to have a m0.tip == m1.tip conjunct too
 *                  which seemed a bit misplaced
 *                  removing that conjunct required very few changes (one in HACL), since ST effect gives it already
 *)
let modifies (s:Set.set rid) (m0:mem) (m1:mem) =
  modifies_just s m0.h m1.h

let modifies_transitively (s:Set.set rid) (m0:mem) (m1:mem) =
  FStar.Monotonic.HyperHeap.modifies s m0.h m1.h

let heap_only (m0:mem) = m0.tip = root

let top_frame (m:mem) = Map.sel m.h m.tip

let modifies_drop_tip (m0:mem) (m1:mem) (m2:mem) (s:Set.set rid)
    : Lemma (fresh_frame m0 m1 /\ m1.tip == m2.tip /\
             modifies_transitively (Set.union s (Set.singleton m1.tip)) m1 m2 ==>
             modifies_transitively s m0 (pop m2))
    = ()

private let lemma_pop_is_popped (m0:mem{poppable m0})
  : Lemma (popped m0 (pop m0))
  = let m1 = pop m0 in
    assert (Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip))

let modifies_one id h0 h1 = modifies_one id h0.h h1.h
let modifies_ref (id:rid) (s:Set.set nat) (h0:mem) (h1:mem) =
  Heap.modifies s (Map.sel h0.h id) (Map.sel h1.h id)

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
  (ensures  (frameOf x <> frameOf x' \/ ~ (as_ref x === as_ref x')))
  [SMTPat (contains h x); SMTPat (x' `unused_in` h)]
let lemma_live_1 #a #a' #rel #rel' h x x' = ()

let above_tip_is_live (#a:Type) (#rel:preorder a) (m:mem) (x:mreference a rel) : Lemma
  (requires (frameOf x `is_above` m.tip))
  (ensures (frameOf x `is_in` m.h))
  = ()

noeq type some_ref =
  | Ref : #a:Type0 -> #rel:preorder a -> mreference a rel -> some_ref

let some_refs = list some_ref

[@"opaque_to_smt"]
private let rec regions_of_some_refs (rs:some_refs) :Tot (Set.set rid) =
  match rs with
  | []         -> Set.empty
  | (Ref r)::tl -> Set.union (Set.singleton (frameOf r)) (regions_of_some_refs tl)

[@"opaque_to_smt"]
private let rec refs_in_region (r:rid) (rs:some_refs) :GTot (Set.set nat) =
  match rs with
  | []         -> Set.empty
  | (Ref x)::tl ->
    Set.union (if frameOf x = r then Set.singleton (as_addr x) else Set.empty)
              (refs_in_region r tl)

[@"opaque_to_smt"]
private let rec modifies_some_refs (i:some_refs) (rs:some_refs) (h0:mem) (h1:mem) :GTot Type0 =
  match i with
  | []         -> True
  | (Ref x)::tl ->
    (modifies_ref (frameOf x) (refs_in_region (frameOf x) rs) h0 h1) /\
    (modifies_some_refs tl rs h0 h1)

[@"opaque_to_smt"]
unfold private let norm_steps :list norm_step =
  [iota; delta; delta_only ["FStar.Monotonic.HyperStack.regions_of_some_refs";
                            "FStar.Monotonic.HyperStack.refs_in_region";
                            "FStar.Monotonic.HyperStack.modifies_some_refs"];
   primops]

[@"opaque_to_smt"]
unfold let mods (rs:some_refs) (h0 h1:mem) :GTot Type0 =
       (norm norm_steps (modifies (regions_of_some_refs rs) h0 h1)) /\
       (norm norm_steps (modifies_some_refs rs rs h0 h1))

////////////////////////////////////////////////////////////////////////////////
let eternal_disjoint_from_tip (h:mem{is_stack_region h.tip})
                              (r:rid{is_eternal_region r /\
                                     r<>root /\
                                     r `is_in` h.h})
   : Lemma (disjoint h.tip r)
   = ()

////////////////////////////////////////////////////////////////////////////////

(*** Untyped views of references *)

(* Definition and ghost decidable equality *)

noeq abstract type aref: Type0 =
| ARef:
    (aref_region: rid) ->
    (aref_aref: Heap.aref) ->
    aref

abstract let dummy_aref : aref = ARef root Heap.dummy_aref

abstract let aref_equal
  (a1 a2: aref)
: Ghost bool
  (requires True)
  (ensures (fun b -> b == true <==> a1 == a2))
= a1.aref_region = a2.aref_region && Heap.aref_equal a1.aref_aref a2.aref_aref

(* Introduction rule *)

abstract let aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
  : Tot aref
  = ARef (frameOf r) (Heap.aref_of (as_ref r))

(* Operators lifted from reference *)

abstract let frameOf_aref
  (a: aref)
: GTot rid
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
= Heap.addr_of_aref a.aref_aref

abstract let aref_as_addr_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (aref_as_addr (aref_of r) == as_addr r)
  [SMTPat (aref_as_addr (aref_of r))]
= Heap.addr_of_aref_of (as_ref r)

abstract let aref_is_mm
  (r: aref)
: GTot bool
= Heap.aref_is_mm r.aref_aref

abstract let is_mm_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (aref_is_mm (aref_of r) == is_mm r)
  [SMTPat (aref_is_mm (aref_of r))]
= Heap.is_mm_aref_of (as_ref r)

abstract let aref_unused_in
  (a: aref)
  (h: mem)
: GTot Type0
= ~ (live_region h a.aref_region) \/
  Heap.aref_unused_in a.aref_aref (Map.sel h.h a.aref_region)

abstract let unused_in_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
  (h: mem)
: Lemma
  (aref_unused_in (aref_of r) h <==> unused_in r h)
  [SMTPat (aref_unused_in (aref_of r) h)]
= Heap.unused_in_aref_of (as_ref r) (Map.sel h.h (frameOf r))

abstract
val contains_aref_unused_in: #a:Type -> #rel: preorder a -> h:mem -> x:mreference a rel -> y:aref -> Lemma
  (requires (contains h x /\ aref_unused_in y h))
  (ensures  (frameOf x <> frameOf_aref y \/ as_addr x <> aref_as_addr y))
  [SMTPat (contains h x); SMTPat (aref_unused_in y h)]
let contains_aref_unused_in #a #rel h x y =
  if frameOf x = frameOf_aref y
  then
    Heap.contains_aref_unused_in (Map.sel h.h (frameOf x)) (as_ref x) y.aref_aref
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
  /\ Heap.aref_live_at (Map.sel h.h a.aref_region) a.aref_aref v rel

abstract
let greference_of
  (a: aref)
  (v: Type)
  (rel: preorder v)
: Ghost (mreference v rel)
  (requires (exists h . aref_live_at h a v rel))
  (ensures (fun _ -> True))
= MkRef a.aref_region (Heap.gref_of a.aref_aref v rel)

abstract
let reference_of
  (h: mem)
  (a: aref)
  (v: Type)
  (rel: preorder v)
: Pure (mreference v rel)
  (requires (aref_live_at h a v rel))
  (ensures (fun x -> aref_live_at h a v rel /\ frameOf x == frameOf_aref a /\ as_addr x == aref_as_addr a /\ is_mm x == aref_is_mm a))
= MkRef a.aref_region (Heap.ref_of (Map.sel h.h a.aref_region) a.aref_aref v rel)

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
= ()

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
