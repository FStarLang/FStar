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

(* let haseq_m_rref (r:rid) (a:Type) (b:reln a)  *)
(*     : Lemma (requires True) *)
(* 	    (ensures (hasEq (m_rref r a b))) *)
(* 	    [SMTPat (hasEq (m_rref r a b))] *)
(*     = () *)

(* val as_rref: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b -> GTot (rref r a) *)
(* let as_rref #r #a #b x = x *)

(* assume HasEq_m_rref: forall (r:rid) (a:Type) (b:reln a).{:pattern (hasEq (m_rref r a b))} hasEq (m_rref r a b) *)
(*
 * AR: the refinement is important here, for as_rref rid was part of the type index
 *)
(*
 * AR: commenting out as_hsref, m_contains, m_unused_in, m_fresh, m_sel as we can now use their HS counterparts
 *)
val as_hsref: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b -> GTot (x:mref a b{HS.frameOf x = r})
let as_hsref #r #a #b x = x

// (* val m_contains : #r:rid -> #a:Type -> #b:reln a -> mr:m_rref r a b -> m:t -> GTot bool *)
// (* let m_contains #r #a #b mr m = HyperHeap.contains_ref (as_rref mr) m *)

let m_contains (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m:mem) = HS.contains m mr

let m_unused_in (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m:mem) = HS.unused_in mr m

(* let m_fresh (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m0:t) (m1:t) : GTot Type0 = *)
(*   HyperHeap.fresh_rref (as_rref mr) m0 m1 *)

let m_fresh (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m0:mem) (m1:mem) : GTot Type0 =
  HyperHeap.fresh_rref (HS.mrref_of mr) m0.h m1.h

// (* val m_sel: #r:rid -> #a:Type -> #b:reln a -> h:t -> m_rref r a b -> GTot a *)
// (* let m_sel #r #a #b h m = HyperHeap.sel h (as_rref m) *)

val m_sel: #r:rid -> #a:Type -> #b:reln a -> h:mem -> m_rref r a b -> GTot a
let m_sel #r #a #b h m = HS.sel h m

(* 17-01-05 m_upd seems unsound (2 missing preconditions) and unused: commenting out for now 
(* val m_upd: #r:rid -> #a:Type -> #b:reln a -> h:t -> m_rref r a b -> a -> GTot t *)
(* let m_upd #r #a #b h m v = HyperHeap.upd h (as_rref m) v *)

val m_upd: #r:rid -> #a:Type -> #b:reln a -> h:mem{live_region h r} -> m_rref r a b -> a -> GTot mem
let m_upd #r #a #b h m v = HS.upd h (as_hsref m) v
*)

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

unfold type stable_on_t (#i:rid) (#a:Type) (#b:reln a) (r:m_rref i a b) (p:(mem -> Tot Type0))
  = HST.stable_on_t #i #a #b r p

abstract type witnessed (#i:rid) (#a:Type) (#b:reln a)
                        (r:m_rref i a b) (p:(mem -> Tot Type0))
  = HST.mr_witnessed r p

(* witnesses a property stable by all updates on p; once we have a witness, there is no need to record that it was obtained using m's monotonicity. *) 
val witness (#r:rid) (#a:Type) (#b:reln a) (m:m_rref r a b) (p:(mem -> Tot Type0))
  :ST unit
      (requires (fun h0      -> p h0   /\ stable_on_t m p))
      (ensures  (fun h0 _ h1 -> h0==h1 /\ witnessed m p))
let witness #r #a #b m p = HST.mr_witness m p

let weaken_witness (#r:rid) (#a:Type) (#b:reln a)
  (m:m_rref r a b) 
  (p:(mem -> GTot Type0){stable_on_t m p})
  (q:(mem -> GTot Type0){stable_on_t m q})
  :Lemma ((forall h. p h ==> q h) /\ witnessed m p ==> witnessed m q)
  = HST.mr_weaken_witness m p q

(* claims a witnessed property holds in the current state *)
val testify (#r:rid) (#a:Type) (#b:reln a)
  (m:m_rref r a b) 
  (p:(mem -> GTot Type0))
  :ST unit (requires (fun _      ->  witnessed m p))
           (ensures (fun h0 _ h1 -> h0==h1 /\ h0 `HS.contains` m /\ p h1))
let testify #r #a #b m p = HST.mr_testify m p

(* 17-01-05 can we prove it from testify? *) 
val testify_forall (#r:rid) (#a:Type) (#b:reln a) (#c:Type) (#p:(c -> mem -> Type0))
  (m:m_rref r a b) 
  ($s:squash (forall (x:c). witnessed m (p x)))
  :ST unit (requires (fun h      -> True))
           (ensures (fun h0 _ h1 -> h0==h1 /\ (forall (x:c). p x h1)))
let testify_forall #r #a #b #p $s = admit ()

(*
 * AR: 12/07: use recall from HyperStack.ST
 *)
val m_recall (#r:rid) (#a:Type) (#b:reln a) (m:m_rref r a b)
  :ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> h0==h1 /\ contains h1 m))
let m_recall #r #a #b m = recall m

(* another instance of monotonic property, this time on the global map of regions; not used much? *)
(*
 * AR: 12/07: rid_exists is simply region_contains_pred from HyperStack.sT
 * and ex_rid is simply HyperStack.ST.rid
 *)
(* another instance of monotonic property, this time on the global map of regions; not used much? *)
let rid_exists (r:rid) (h:mem) = region_contains_pred r h
// ex_rid: The type of a region id that is known to exist now and for ever more
type ex_rid = r:rid{HST.witnessed (region_contains_pred r)}

assume val ex_rid_of_rid: r:rid -> ST ex_rid
  (fun h -> True)
(fun h0 r' h1 -> r=r' /\ h0==h1)
