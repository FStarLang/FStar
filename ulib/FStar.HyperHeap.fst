(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi, and Microsoft Research

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
module FStar.HyperHeap

include FStar.Monotonic.HyperHeap
type rref (id:rid) (a:Type) = mrref id a (FStar.Heap.trivial_preorder a)


(*** Untyped views of references *)

(* Definition and ghost decidable equality *)

abstract let aref (i: rid) : Type0 = Heap.aref

abstract let dummy_aref (i: rid) : aref i = Heap.dummy_aref

abstract let aref_equal
  (#i: rid)
  (a1 a2: aref i)
: Ghost bool
  (requires True)
  (ensures (fun b -> b == true <==> a1 == a2))
= Heap.aref_equal a1 a2

(* Introduction rule *)

abstract let aref_of
  (#i: rid)
  (#a: Type)
  (r: rref i a)
: Tot (aref i)
= Heap.aref_of r

(* Operators lifted from rref *)

abstract let addr_of_aref
  (#id:rid)
  (r:aref id)
: GTot nat
= Heap.addr_of_aref r

abstract let addr_of_aref_of
  (#id:rid)
  (#a: Type)
  (r: rref id a)
: Lemma
  (addr_of r == addr_of_aref (aref_of r))
  [SMTPat (addr_of_aref (aref_of r))]
= Heap.addr_of_aref_of r

abstract let aref_is_mm
  (#id: rid)
  (r: aref id)
: GTot bool
= Heap.aref_is_mm r

abstract let is_mm_aref_of
  (#id: rid)
  (#a: Type)
  (r: rref id a)
: Lemma
  (is_mm r == aref_is_mm (aref_of r))
  [SMTPat (aref_is_mm (aref_of r))]
= Heap.is_mm_aref_of r

abstract let aref_unused_in
  (#i: rid)
  (r: aref i)
  (m: t)
: GTot Type0
= not (Map.contains m i) \/
  Heap.aref_unused_in r (Map.sel m i)

abstract let unused_in_aref_of
  (#a: Type)
  (#i: rid)
  (r: rref i a)
  (m: t)
: Lemma
  (aref_unused_in (aref_of r) m <==> unused_in r m)
  [SMTPat (aref_unused_in (aref_of r))]
= Heap.unused_in_aref_of r (Map.sel m i)

abstract
val contains_ref_aref_unused_in: #i: rid -> #a:Type ->  h:t -> x:rref i a -> y:aref i -> Lemma
  (requires (contains_ref x h /\ aref_unused_in y h))
  (ensures  (addr_of x <> addr_of_aref y))
let contains_ref_aref_unused_in #i #a h x y = Heap.contains_aref_unused_in (Map.sel h i) x y

(* Elimination rule *)

abstract let aref_live_at (m: t) (#i: rid) (a: aref i) (v: Type) : GTot Type0 =
  Map.contains m i /\
  Heap.aref_live_at (Map.sel m i) a v

abstract let grref_of
  (#i: rid)
  (a: aref i)
  (v: Type0)
: Ghost (rref i v)
  (requires (exists m . aref_live_at m a v))
  (ensures (fun x -> True))
= Heap.gref_of a v

abstract let rref_of
  (m: t)
  (#i: rid)
  (a: aref i)
  (v: Type)
: Pure (rref i v)
  (requires (aref_live_at m a v))
  (ensures (fun x -> aref_live_at m a v /\ x == grref_of a v))
= Heap.ref_of (Map.sel m i) a v

abstract
let aref_live_at_aref_of
  (m: t)
  (#i: rid)
  (#v: Type0)
  (r: rref i v)
: Lemma
  (ensures (aref_live_at m (aref_of r) v <==> contains_ref r m))
  [SMTPat (aref_live_at m (aref_of r) v)]
= ()

abstract
let contains_ref_grref_of
  (m: t)
  (#i: rid)
  (a: aref i)
  (v: Type0)
: Lemma
  (requires (exists h' . aref_live_at h' a v))
  (ensures ((exists h' . aref_live_at h' a v) /\ (contains_ref (grref_of a v) m <==> aref_live_at m a v)))
  [SMTPatOr [
    [SMTPat (contains_ref (grref_of a v) m)];
    [SMTPat (aref_live_at m a v)];
  ]]
= ()

abstract
let aref_of_grref_of
  (#i: rid)
  (a: aref i)
  (v: Type0)
: Lemma
  (requires (exists h . aref_live_at h a v))
  (ensures ((exists h. aref_live_at h a v) /\ aref_of (grref_of a v) == a))
  [SMTPat (aref_of (grref_of a v))]
= ()

abstract
let grref_of_aref_of
  (#i: rid)
  (#v: Type0)
  (r: rref i v)
: Lemma
  (requires (exists h . contains_ref r h))
  (ensures ((exists h . contains_ref r h) /\ grref_of (aref_of r) v == r))
  [SMTPat (grref_of (aref_of r) v)]
= ()

(* Operators lowered to rref *)

abstract
let addr_of_grref_of
  (#i: rid)
  (a: aref i)
  (t: Type0)
: Lemma
  (requires (exists h . aref_live_at h a t))
  (ensures ((exists h . aref_live_at h a t) /\ addr_of (grref_of a t) == addr_of_aref a))
  [SMTPat (addr_of (grref_of a t))]
= ()

abstract
let is_mm_grref_of
  (#i: rid)
  (a: aref i)
  (t: Type0)
: Lemma
  (requires (exists h . aref_live_at h a t))
  (ensures ((exists h . aref_live_at h a t) /\ is_mm (grref_of a t) == aref_is_mm a))
  [SMTPat (is_mm (grref_of a t))]
= ()

abstract
let unused_in_gref_of
  (#i: rid)
  (a: aref i)
  (v: Type0)
  (h: t)
: Lemma
  (requires (exists h . aref_live_at h a v))
  (ensures ((exists h . aref_live_at h a v) /\ (unused_in (grref_of a v) h <==> aref_unused_in a h)))
  [SMTPat (unused_in (grref_of a v) h)]
= ()
