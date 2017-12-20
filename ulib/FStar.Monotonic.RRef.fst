module FStar.Monotonic.RRef

open FStar
open FStar.HyperHeap

open FStar.HyperStack
open FStar.HyperStack.ST

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let reln (a:Type) = Preorder.preorder a

let monotonic (a:Type) (b:reln a) = Preorder.preorder_rel b

(*
 * AR: adding is_eternal_region refinement, since mrefs are allocated using ralloc
 *)
type rid = r:rid{is_eternal_region r}

(*
 * AR: HS.ref, means it is not mm.
 * This along with rid above is essential to justify recall.
 *)
(*
 * AR: 12/07: now reln is a preorder, but we should already be using it as such
 *)
type m_rref (r:rid) (a:Type) (b:reln a) = HST.m_rref r a b

val as_hsref: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b -> GTot (x:mref a b{HS.frameOf x = r})
let as_hsref #r #a #b x = x

let m_contains (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m:mem) = HS.contains m mr
let m_unused_in (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m:mem) = HS.unused_in mr m

let m_fresh (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m0:mem) (m1:mem) : GTot Type0 =
  HyperHeap.fresh_rref (HS.mrref_of mr) m0.h m1.h

val m_sel: #r:rid -> #a:Type -> #b:reln a -> h:mem -> m_rref r a b -> GTot a
let m_sel #r #a #b h m = HS.sel h m

(* allocates a reference and an associated monotonic-update condition *)
inline_for_extraction
val m_alloc (#a:Type) (#b:reln a) (r:rid) (init:a)
  :ST (m_rref r a b)
      (requires (fun _ -> witnessed (region_contains_pred r)))
      (ensures  (fun h0 (m:m_rref r a b) h1 -> ralloc_post r init h0 m h1))
inline_for_extraction
let m_alloc #a #b r init = HST.ralloc r init

inline_for_extraction
val m_read (#r:rid) (#a:Type) (#b:reln a) (x:m_rref r a b)
  :ST a (requires (fun h -> True)) (ensures  (deref_post x))
inline_for_extraction
let m_read #r #a #b x = !x

inline_for_extraction
val m_write (#r:rid) (#a:Type) (#b:reln a) (x:m_rref r a b) (v:a)
  :ST unit
      (requires (fun h0 -> h0 `contains` x /\ b (HS.sel h0 x) v))
      (ensures  (assign_post x v))
inline_for_extraction
let m_write #r #a #b x v = x := v

unfold type stable_on_t (#i:rid) (#a:Type) (#b:reln a) (r:m_rref i a b) (p:HST.mem_predicate)
  = HST.stable_on_t #i #a #b r p

type witnessed (p:mem_predicate) = HST.witnessed p

(* witnesses a property stable by all updates on p; once we have a witness, there is no need to record that it was obtained using m's monotonicity. *) 
val witness (#r:rid) (#a:Type) (#b:reln a) (m:m_rref r a b) (p:HST.mem_predicate)
  :ST unit
      (requires (fun h0      -> p h0   /\ stable_on_t m p))
      (ensures  (fun h0 _ h1 -> h0==h1 /\ witnessed p))
let witness #r #a #b m p = HST.mr_witness m p

let weaken_witness (#r:rid) (#a:Type) (#b:reln a)
  (m:m_rref r a b) 
  (p:HST.mem_predicate{stable_on_t m p})
  (q:HST.mem_predicate{stable_on_t m q})
  :Lemma ((forall h. p h ==> q h) /\ witnessed p ==> witnessed q)
  = HST.mr_weaken_witness m p q

(* claims a witnessed property holds in the current state *)
val testify (p:mem_predicate)
  :ST unit (requires (fun _      ->  witnessed p))
           (ensures (fun h0 _ h1 -> h0==h1 /\ p h1))
let testify p = HST.gst_recall p

(* 17-01-05 can we prove it from testify? *) 
val testify_forall (#c:Type) (#p:(c -> mem -> Type0))
  ($s:squash (forall (x:c). witnessed (p x)))
  :ST unit (requires (fun h      -> True))
           (ensures (fun h0 _ h1 -> h0==h1 /\ (forall (x:c). p x h1)))
let testify_forall #c #p $s = admit ()

(*
 * AR: 12/07: use recall from HyperStack.ST
 *)
val m_recall (#r:rid) (#a:Type) (#b:reln a) (m:m_rref r a b)
  :ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> h0==h1 /\ contains h1 m))
let m_recall #r #a #b m = recall m

(* another instance of monotonic property, this time on the global map of regions; not used much? *)
(* another instance of monotonic property, this time on the global map of regions; not used much? *)
let rid_exists (r:rid) (h:mem) = region_contains_pred r h
// ex_rid: The type of a region id that is known to exist now and for ever more
type ex_rid = r:rid{HST.witnessed (region_contains_pred r)}

assume val ex_rid_of_rid: r:rid -> ST ex_rid
  (fun h -> True)
  (fun h0 r' h1 -> r=r' /\ h0==h1)
