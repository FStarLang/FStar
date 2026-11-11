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

(** Main source-program proof interface. A typed Hoare triple is entailment
    into an abstract WP with postconditions over the expression's result type.
    Clients compose value, context/let/sequence, frame, consequence, fork, and
    primitive rules; no trace or native-action witness is a client premise.

    Ordinary triples have all invariants closed at source-step boundaries.
    Atomic triples describe one value-producing step under an explicit OPEN
    mask. Invariant and ghost-update rules preserve exposed bodies and masks;
    an ordinary multi-step proof cannot substitute for an atomic premise.
    Physical allocation is a source step; ghost allocation is absorbed before
    a non-value. HeapLang.Adequacy proves soundness for this interface once. *)

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
val wp_value (#t:ty) (e:expr [] t) (v:value t) (q:post t)
  : Lemma (requires to_val e == Some v) (ensures wp e q == q v)
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

val context_rule (#a #b:ty) (k:context a b) (p:S.slprop) (e:expr [] a)
  (mid:post a) (q:post b)
  : Lemma
      (requires hoare p e mid /\ (forall v. hoare (mid v) (fill k (Val v)) q))
      (ensures hoare p (fill k e) q)

val eq (x y:int)
  : Lemma (hoare S.emp (Eq (Val x) (Val y)) (returns_value (x = y)))
val if_value (#t:ty) (p:S.slprop) (b:bool) (yes no:expr [] t) (q:post t)
  : Lemma (requires hoare p (if b then yes else no) q)
      (ensures hoare p (If (Val b) yes no) q)

let exposed (p:S.slprop) = S.somewhere (S.later p)
val atomic (#t:ty) (mask:S.inames) (p:S.slprop) (e:expr [] t) (q:post t) : prop
val atomic_nonvalue (#t:ty) (mask:S.inames) (p:S.slprop) (e:expr [] t) (q:post t)
  : Lemma (requires atomic mask p e q) (ensures to_val e == None)
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

let later_post (#t:ty) (q:post t) (v:value t) = S.later (q v)

(** The actual source step eliminates the returned guard. This rule cannot
    eliminate a later before a value, nor can it be iterated inside an atomic
    proof to charge the same source step more than once. *)
val atomic_to_hoare_later (#t:ty) (p:S.slprop) (e:expr [] t) (q:post t)
  : Lemma (requires atomic Pulse.Lib.GhostSet.empty p e (later_post q))
      (ensures hoare p e q)

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

let cas_post (r:PulseCore.Heap.core_ref) (old expected desired:int) (success:bool) =
  S.star (C.points_to r (if success then desired else old))
    (S.pure (success == (old = expected)))
val atomic_cas (mask:S.inames) (r:PulseCore.Heap.core_ref) (old expected desired:int)
  : Lemma (atomic mask (C.points_to r old)
      (Cas (Val r) (Val expected) (Val desired)) (cas_post r old expected desired))
val cas (r:PulseCore.Heap.core_ref) (old expected desired:int)
  : Lemma (hoare (C.points_to r old)
      (Cas (Val r) (Val expected) (Val desired)) (cas_post r old expected desired))

let allocation_post (v:int) (r:PulseCore.Heap.core_ref) = C.points_to r v
val atomic_alloc (mask:S.inames) (v:int)
  : Lemma (atomic mask S.emp (Alloc (Val v)) (allocation_post v))
val alloc (v:int)
  : Lemma (hoare S.emp (Alloc (Val v)) (allocation_post v))

// Ghost allocation is absorbed at the next source step, not at a value.
val allocate_invariant (#t:ty) (p pre:S.slprop) (e:expr [] t) (q:post t)
  (proof:(i:S.iref -> Lemma (hoare (S.star (S.inv i p) pre) e q)))
  : Lemma (requires to_val e == None) (ensures hoare (S.star p pre) e q)

val update (before after:S.inames) (p q:S.slprop) : prop
val update_entails (mask:S.inames) (p q:S.slprop)
  : Lemma (requires S.implies p q) (ensures update mask mask p q)
val update_trans (before middle after:S.inames) (p q r:S.slprop)
  : Lemma (requires update before middle p q /\ update middle after q r)
      (ensures update before after p r)
val update_frame (before after:S.inames) (p q f:S.slprop)
  : Lemma (requires update before after p q)
      (ensures update before after (S.star p f) (S.star q f))
val update_exists (#a:Type0) (before after:S.inames) (p:a -> S.slprop) (q:S.slprop)
  : Lemma (requires forall x. update before after (p x) q)
      (ensures update before after (S.op_exists_Star p) q)
val open_invariant (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)}) (p:S.slprop)
  : Lemma (update mask (S.add_inv mask i) (S.inv i p) (S.star (S.inv i p) (exposed p)))
val close_invariant (mask:S.inames) (i:S.iref{not (S.mem_inv mask i)}) (p:S.slprop)
  : Lemma (update (S.add_inv mask i) mask (S.star (S.inv i p) (exposed p)) (S.inv i p))
let allocated (p:S.slprop) = S.op_exists_Star (fun (i:S.iref) -> S.inv i p)
val update_allocate (p:S.slprop)
  : Lemma (update Pulse.Lib.GhostSet.empty Pulse.Lib.GhostSet.empty p (allocated p))
val update_later_elim (mask:S.inames) (p:S.slprop)
  : Lemma (update mask mask (S.star (S.later p) (S.later_credit 1)) p)
val update_hoare (#t:ty) (p mid:S.slprop) (e:expr [] t) (q:post t)
  : Lemma
      (requires to_val e == None /\
        update Pulse.Lib.GhostSet.empty Pulse.Lib.GhostSet.empty p mid /\ hoare mid e q)
      (ensures hoare p e q)
val atomic_updates (#t:ty) (outer inner:S.inames) (p mid:S.slprop)
  (e:expr [] t) (q post:post t)
  : Lemma
      (requires update outer inner p mid /\ atomic inner mid e q /\
        (forall v. update inner outer (q v) (post v)))
      (ensures atomic outer p e post)

val atomic_pure_pre (#t:ty) (mask:S.inames) (p:S.slprop) (fact:prop)
  (e:expr [] t) (q:post t)
  (proof:(unit -> Lemma (requires fact) (ensures atomic mask p e q)))
  : Lemma (requires to_val e == None)
      (ensures atomic mask (S.star p (S.pure fact)) e q)
val update_pure_pre (before after:S.inames) (p q:S.slprop) (fact:prop)
  (proof:(unit -> Lemma (requires fact) (ensures update before after p q)))
  : Lemma (update before after (S.star p (S.pure fact)) q)
val frame_constant (#t:ty) (p:S.slprop) (e:expr [] t) (q f:S.slprop)
  : Lemma (requires hoare p e (constant_post q))
      (ensures hoare (S.star p f) e (constant_post (S.star q f)))
