(*
   Copyright 2026 Microsoft Research

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
module Pulse.Extrinsic.HeapLang.Proof

open Pulse.Extrinsic.HeapLang
module S = PulseCore.IndirectionTheorySep
module C = Pulse.Extrinsic.HeapLang.Logic

let post (t:ty) = value t -> S.slprop
let constant_post (#t:ty) (p:S.slprop) (_:value t) = p
let framed_post (#t:ty) (q:post t) (f:S.slprop) (v:value t) = S.star (q v) f
let prepend_post (#t:ty) (p:S.slprop) (q:post t) (v:value t) = S.star p (q v)
let returns_value (#t:ty) (expected:value t) (v:value t) = S.pure (v == expected)
let read_post (r:PulseCore.Heap.core_ref) (old:int) (v:int) =
  S.star (C.points_to r old) (S.pure (v == old))
val wp (#t:ty) (e:expr [] t) (q:post t) : S.slprop
let hoare (#t:ty) (p:S.slprop) (e:expr [] t) (q:post t) = S.implies p (wp e q)

val consequence (#t:ty) (p p':S.slprop) (e:expr [] t) (q q':post t)
  : Lemma
      (requires hoare p e q /\ S.implies p' p /\ (forall v. S.implies (q v) (q' v)))
      (ensures hoare p' e q')
val frame (#t:ty) (p:S.slprop) (e:expr [] t) (q:post t) (f:S.slprop)
  : Lemma (requires hoare p e q)
      (ensures hoare (S.star p f) e (framed_post q f))
val pure_pre (#t:ty) (p:S.slprop) (fact:prop) (e:expr [] t) (q:post t)
  (proof:(unit -> Lemma (requires fact) (ensures hoare p e q)))
  : Lemma (hoare (S.star p (S.pure fact)) e q)
val value_rule (#t:ty) (p:S.slprop) (v:value t) (q:post t)
  : Lemma (requires S.implies p (q v)) (ensures hoare p (Val v) q)
val let_rule (#a #b:ty) (p:S.slprop) (bound:expr [] a) (body:expr [a] b)
  (mid:post a) (q:post b)
  : Lemma
      (requires hoare p bound mid /\ (forall v. hoare (mid v) (substitute v body) q))
      (ensures hoare p (Let bound body) q)
val sequence (#t:ty) (p mid:S.slprop) (first:expr [] TUnit) (rest:expr [] t) (q:post t)
  : Lemma (requires hoare p first (constant_post mid) /\ hoare mid rest q)
      (ensures hoare p (Seq first rest) q)
val fork (parent child:S.slprop) (e:expr [] TUnit) (q:post TUnit)
  : Lemma (requires S.implies parent (q ()) /\ hoare child e (constant_post S.emp))
      (ensures hoare (S.star parent child) (Fork e) q)
val add (x y:int)
  : Lemma (hoare S.emp (Add (Val x) (Val y)) (returns_value (x + y)))

let exposed (p:S.slprop) = S.somewhere (S.later p)
val atomic (#t:ty) (mask:S.inames) (p:S.slprop) (e:expr [] t) (q:post t) : prop
val atomic_consequence (#t:ty) (mask:S.inames) (p p':S.slprop)
  (e:expr [] t) (q q':post t)
  : Lemma
      (requires atomic mask p e q /\ S.implies p' p /\
        (forall v. S.implies (q v) (q' v)))
      (ensures atomic mask p' e q')
val atomic_frame (#t:ty) (mask:S.inames) (p:S.slprop) (e:expr [] t) (q:post t) (f:S.slprop)
  : Lemma (requires atomic mask p e q)
      (ensures atomic mask (S.star p f) e (framed_post q f))
val atomic_exists (#a:Type0) (#t:ty) (mask:S.inames)
  (p:a -> S.slprop) (e:expr [] t) (q:post t)
  : Lemma (requires to_val e == None /\ (forall x. atomic mask (p x) e q))
      (ensures atomic mask (S.op_exists_Star p) e q)
val atomic_invariant (#t:ty) (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)})
  (p pre:S.slprop) (e:expr [] t) (q:post t)
  : Lemma
      (requires atomic (S.add_inv mask i) (S.star (exposed p) pre) e
        (prepend_post (exposed p) q))
      (ensures atomic mask (S.star (S.inv i p) pre) e
        (prepend_post (S.inv i p) q))
val atomic_to_hoare (#t:ty) (p:S.slprop) (e:expr [] t) (q:post t)
  : Lemma (requires atomic Pulse.Lib.GhostSet.empty p e q) (ensures hoare p e q)

val atomic_load (mask:S.inames) (r:PulseCore.Heap.core_ref) (old:int)
  : Lemma (atomic mask (C.points_to r old) (Load (Val r))
      (read_post r old))
val atomic_store (mask:S.inames) (r:PulseCore.Heap.core_ref) (old desired:int)
  : Lemma (atomic mask (C.points_to r old) (Store (Val r) (Val desired))
      (constant_post (C.points_to r desired)))
val load (r:PulseCore.Heap.core_ref) (old:int)
  : Lemma (hoare (C.points_to r old) (Load (Val r))
      (read_post r old))
val store (r:PulseCore.Heap.core_ref) (old desired:int)
  : Lemma (hoare (C.points_to r old) (Store (Val r) (Val desired))
      (constant_post (C.points_to r desired)))

// Ghost allocation is absorbed at the next source step, not at a value.
val allocate_invariant (#t:ty) (p pre:S.slprop) (e:expr [] t) (q:post t)
  (proof:(i:S.iref -> Lemma (hoare (S.star (S.inv i p) pre) e q)))
  : Lemma (requires to_val e == None) (ensures hoare (S.star p pre) e q)
