module FStar.HyperStack

include FStar.Monotonic.HyperStack

open FStar.HyperHeap

type reference (a:Type) = mreference a (Heap.trivial_preorder a)

let stackref (a:Type) = mstackref a (Heap.trivial_preorder a)
let ref (a:Type) = mref a (Heap.trivial_preorder a)

let mmstackref (a:Type) = mmmstackref a (Heap.trivial_preorder a)
let mmref (a:Type) = mmmref a (Heap.trivial_preorder a)
type s_ref (i:rid) (a:Type) = s_mref i a (Heap.trivial_preorder a)

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
  (r: reference t)
: Tot aref
= ARef r.id (HH.aref_of r.ref)

(* Operators lifted from reference *)

abstract let frameOf_aref
  (a: aref)
: GTot HH.rid
= a.aref_region

abstract let frameOf_aref_of
  (#t: Type)
  (r: reference t)
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
  (r: reference t)
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
  (r: reference t)
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
  (r: reference t)
  (h: mem)
: Lemma
  (aref_unused_in (aref_of r) h <==> unused_in r h)
  [SMTPat (aref_unused_in (aref_of r))]
= HH.unused_in_aref_of r.ref h.h

abstract
val contains_aref_unused_in: #a:Type ->  h:mem -> x:reference a -> y:aref -> Lemma
  (requires (contains h x /\ aref_unused_in y h))
  (ensures  (frameOf x <> frameOf_aref y \/ as_addr x <> aref_as_addr y))
  [SMTPat (contains h x); SMTPat (aref_unused_in y h)]
let contains_aref_unused_in #a h x y =
  if frameOf x = frameOf_aref y
  then HH.contains_ref_aref_unused_in h.h x.ref y.aref_aref
  else ()

(* Elimination rule *)

abstract
let aref_live_at
  (h: mem)
  (a: aref)
  (v: Type)
: GTot Type0
= live_region h a.aref_region
  /\ HH.aref_live_at h.h a.aref_aref v

abstract
let greference_of
  (a: aref)
  (v: Type)
: Ghost (reference v)
  (requires (exists h . aref_live_at h a v))
  (ensures (fun _ -> True))
= MkRef a.aref_region (HH.grref_of a.aref_aref v)

abstract
let reference_of
  (h: mem)
  (a: aref)
  (v: Type)
: Pure (reference v)
  (requires (aref_live_at h a v))
  (ensures (fun x -> aref_live_at h a v /\ x == greference_of a v))
= MkRef a.aref_region (HH.rref_of h.h a.aref_aref v)

abstract
let aref_live_at_aref_of
  (h: mem)
  (#t: Type0)
  (r: reference t)
: Lemma
  (aref_live_at h (aref_of r) t <==> contains h r)
  [SMTPat (aref_live_at h (aref_of r) t)]
= ()

abstract
let contains_greference_of
  (h: mem)
  (a: aref)
  (t: Type0)
: Lemma
  (requires (exists h' . aref_live_at h' a t))
  (ensures ((exists h' . aref_live_at h' a t) /\ (contains h (greference_of a t) <==> aref_live_at h a t)))
  [SMTPatOr [
    [SMTPat (contains h (greference_of a t))];
    [SMTPat (aref_live_at h a t)];
  ]]
= ()

abstract
let aref_of_greference_of
  (a: aref)
  (v: Type0)
: Lemma
  (requires (exists h' . aref_live_at h' a v))
  (ensures ((exists h' . aref_live_at h' a v) /\ aref_of (greference_of a v) == a))
  [SMTPat (aref_of (greference_of a v))]
= ()

abstract
let greference_of_aref_of
  (#v: Type0)
  (a: reference v)
: Lemma
  (requires (exists h' . contains h' a))
  (ensures ((exists h' . contains h' a) /\ greference_of (aref_of a) v == a))
  [SMTPat (greference_of (aref_of a) v)]
= ()

(* Operators lowered to rref *)

abstract let frameOf_greference_of
  (h: mem)
  (a: aref)
  (t: Type)
: Lemma
  (requires (exists h . aref_live_at h a t))
  (ensures ((exists h . aref_live_at h a t) /\ frameOf (greference_of a t) == frameOf_aref a))
  [SMTPat (frameOf (greference_of a t))]
= ()

abstract
let as_addr_greference_of
  (a: aref)
  (t: Type0)
: Lemma
  (requires (exists h . aref_live_at h a t))
  (ensures ((exists h . aref_live_at h a t) /\ as_addr (greference_of a t) == aref_as_addr a))
  [SMTPat (as_addr (greference_of a t))]
= assert (addr_of (grref_of a.aref_aref t) == addr_of_aref a.aref_aref)

abstract
let is_mm_greference_of
  (a: aref)
  (t: Type0)
: Lemma
  (requires (exists h . aref_live_at h a t))
  (ensures ((exists h . aref_live_at h a t) /\ is_mm (greference_of a t) == aref_is_mm a))
  [SMTPat (is_mm (greference_of a t))]
= ()  

abstract
let unused_in_greference_of
  (a: aref)
  (t: Type0)
  (h: mem)
: Lemma
  (requires (exists h . aref_live_at h a t))
  (ensures ((exists h . aref_live_at h a t) /\ (unused_in (greference_of a t) h <==> aref_unused_in a h)))
  [SMTPat (unused_in (greference_of a t))]
= ()
