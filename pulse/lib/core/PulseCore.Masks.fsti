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
module PulseCore.Masks

(** Paired-mask actions over the existing Pulse semantics. Pulse.Lib.Core
exports the computation types and combinators with extraction annotations;
Pulse.Lib.Core.Inv exports separate opening and closing of core invariants.
The masks name open invariants, not the footprint of an atomic computation. *)

open FStar.Ghost
open PulseCore.InstantiatedSemantics
open PulseCore.Action
open PulseCore.Atomic
open PulseCore.Observability
open Pulse.Lib.Loc
module Sep = PulseCore.IndirectionTheorySep

val action (a:Type u#a) (obs:observability)
  (before after:inames) (pre:slprop) (post:a -> slprop) : Type u#(max 4 a)

[@@erasable]
val gaction (a:Type u#a) (before after:inames)
  (pre:slprop) (post:a -> slprop) : Type u#(max 4 a)

val return_action (#a:Type u#a) (mask:inames) (x:a) (post:a -> slprop)
  : action a Neutral mask mask (post x) post

val bind_action (#a:Type u#a) (#b:Type u#b)
  (#o1:observability) (#o2:observability { at_most_one_observable o1 o2 })
  (#m1 #m2 #m3:inames) (#p:slprop) (#q:a -> slprop) (#r:b -> slprop)
  (f:action a o1 m1 m2 p q)
  (g:(x:a -> action b o2 m2 m3 (q x) r))
  : action b (join_obs o1 o2) m1 m3 p r

val frame_action (#a:Type u#a) (#o:observability)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (r:slprop) (f:action a o m1 m2 p q)
  : action a o m1 m2 (p ** r) (fun x -> q x ** r)

val lift_atomic_action (#a:Type u#a) (#o:observability)
  (#opens:inames) (#p:slprop) (#q:a -> slprop)
  (mask:inames { mask /! opens })
  (f:stt_atomic a #o opens p q)
  : action a o mask mask p q

val lift_ghost_action (#a:Type u#a) (#opens:inames) (#p:slprop) (#q:a -> slprop)
  (mask:inames { mask /! opens })
  (f:stt_ghost a opens p q)
  : gaction a mask mask p q

val ghost_to_action (#a:Type u#a)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (f:gaction a m1 m2 p q)
  : action (erased a) Neutral m1 m2 p (fun x -> q x)

val bind_gaction (#a:Type u#a) (#b:Type u#b)
  (#m1 #m2 #m3:inames) (#p:slprop) (#q:a -> slprop) (#r:b -> slprop)
  (f:gaction a m1 m2 p q)
  (g:(x:a -> gaction b m2 m3 (q x) r))
  : gaction b m1 m3 p r

val frame_gaction (#a:Type u#a)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (r:slprop) (f:gaction a m1 m2 p q)
  : gaction a m1 m2 (p ** r) (fun x -> q x ** r)

val action_to_ghost (#a:Type u#a)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (f:action a Neutral m1 m2 p q)
  : gaction a m1 m2 p q

val sub_gaction (#a:Type u#a) (#m1 #m2:inames)
  (#p:slprop) (#q:a -> slprop)
  (p':slprop { p == p' })
  (q':(a -> slprop) { forall x. q x == q' x })
  (f:gaction a m1 m2 p q)
  : gaction a m1 m2 p' q'

val reindex_gaction (#a:Type u#a) (#m1 #m2:inames)
  (#p:slprop) (#q:a -> slprop)
  (before:inames { before == m1 }) (after:inames { after == m2 })
  (f:gaction a m1 m2 p q)
  : gaction a before after p q

val localize_gaction (#a:Type u#a) (#before #after:inames)
  (#pre:slprop) (#post:a -> slprop) (l:loc_id)
  (f:gaction a before after pre post)
  : gaction a before after (Sep.on l pre) (fun x -> Sep.on l (post x))

val finish_gaction (#a:Type u#a) (#m1 #m2:inames) (#p:slprop)
  (x:a) (post:a -> slprop) (f:gaction unit m1 m2 p (fun _ -> post x))
  : action a Neutral m1 m2 p post

val run_action (#a:Type0) (#o:observability) (#p:slprop) (#q:a -> slprop)
  (opens:inames)
  (f:(mask:inames { mask /! opens } -> action a o mask mask p q))
  : stt_atomic a #o opens p q

val run_closed_action (#a:Type0) (#o:observability) (#p:slprop) (#q:a -> slprop)
  (f:action a o emp_inames emp_inames p q)
  : stt_atomic a #o (GhostSet.complement emp_inames) p q

val open_invariant (mask:inames) (i:iref { not (mem_inv mask i) }) (p:slprop)
  : gaction unit mask (add_inv mask i)
      (inv i p) (fun _ -> inv i p ** Sep.somewhere (later p))

val close_invariant (mask:inames) (i:iref { not (mem_inv mask i) }) (p:slprop)
  : gaction unit (add_inv mask i) mask
      (inv i p ** Sep.somewhere (later p)) (fun _ -> inv i p)