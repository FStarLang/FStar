module Pulse.Lib.LogicalAtomicity.Masks

(**
Mask-changing atomic actions: the semantic foundation of logical atomicity.

An action may temporarily remove invariant bodies from the ambient invariant
resource, provided its output mask records exactly which invariants remain
open. This decouples opening from closing without changing Pulse's checker or
its lexically scoped `with_invariants` construct. Compose ghost steps around
at most one observable step, then use a balanced runner to return to Pulse.

Unlike Iris's masks of enabled invariants, `before` and `after` are sets of
OPEN invariants: opening adds a name. They also differ from Pulse's `opens`
footprint, which bounds the invariants an ordinary atomic computation may
open. A lifted computation's footprint must be disjoint from the current mask.

The -model.fst verifies these operations against Pulse's existing semantics.
Extraction erases masks, assertions, and ghost actions, retaining sequencing
and the lifted primitive. This is not a transaction implementation: it cannot
make multiple observable operations atomic, or run with an unbalanced mask.
See README.md for the Iris comparison and the prototype's remaining gaps.
*)

open Pulse.Lib.Core
open PulseCore.Observability
open FStar.Ghost
open FStar.ExtractAs
module I = Pulse.Lib.Core.Inv

(** A frame-preserving step from `pre` at `before` to `post` at `after`.
`Neutral` steps change only ghost state; `Observable` permits one physical step.
This type is a semantic action, not an ordinary Pulse computation. *)
[@@extract_as_impure_effect]
val action (a:Type u#a) (obs:observability)
  (before after:inames) (pre:slprop) (post:a -> slprop) : Type u#(max 4 a)

(** The erased, ghost-only counterpart of `action`. Its result cannot be used
to compute runtime data. Distinct masks still track unclosed invariants. *)
[@@erasable]
val gaction (a:Type u#a) (before after:inames)
  (pre:slprop) (post:a -> slprop) : Type u#(max 4 a)

(** Return a value without changing resources, the mask, or observable state. *)
inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (_:unit) (x:a) (_:unit) -> x))]
val return (#a:Type u#a) (mask:inames) (x:a) (post:a -> slprop)
  : action a Neutral mask mask (post x) post

(** Sequence matching masks and intermediate assertions. The observability
constraint rejects two observable components even if their resources match. *)
inline_for_extraction
[@@extract_as (`(fun (#a #b:Type0) (#o1 #o2 #m1 #m2 #m3 #p #q #r:unit)
  (f:a) (g:a -> Dv b) -> g f))]
val bind (#a:Type u#a) (#b:Type u#b)
  (#o1:observability) (#o2:observability { at_most_one_observable o1 o2 })
  (#m1 #m2 #m3:inames) (#p:slprop) (#q:a -> slprop) (#r:b -> slprop)
  (f:action a o1 m1 m2 p q)
  (g:(x:a -> action b o2 m2 m3 (q x) r))
  : action b (join_obs o1 o2) m1 m3 p r

(** Preserve an unrelated spatial resource across the action. This follows
from universal quantification over frames in the semantic implementation. *)
inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#o #m1 #m2 #p #q:unit) (_:unit) (f:a) -> f))]
val frame (#a:Type u#a) (#o:observability)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (r:slprop) (f:action a o m1 m2 p q)
  : action a o m1 m2 (p ** r) (fun x -> q x ** r)

(** Embed an existing atomic computation without changing the open mask.
Disjointness prevents it from reopening an invariant already held outside it. *)
inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#o #opens #p #q:unit) (_:unit) (f:a) -> f))]
val lift_atomic (#a:Type u#a) (#o:observability)
  (#opens:inames) (#p:slprop) (#q:a -> slprop)
  (mask:inames { mask /! opens })
  (f:stt_atomic a #o opens p q)
  : action a o mask mask p q

(** Embed an ordinary ghost computation, subject to the same footprint
disjointness as `lift_atomic`; no observable-step allowance is consumed. *)
val lift_ghost (#a:Type u#a) (#opens:inames) (#p:slprop) (#q:a -> slprop)
  (mask:inames { mask /! opens })
  (f:stt_ghost a opens p q)
  : gaction a mask mask p q

// Erase the result as well as the ghost computation when entering action code.
inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#m1 #m2 #p #q:unit) (_:unit) -> ()))]
val ghost_to_action (#a:Type u#a)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (f:gaction a m1 m2 p q)
  : action (erased a) Neutral m1 m2 p (fun x -> q x)

(** Ghost sequencing with an explicit intermediate mask. No physical step is
introduced, so arbitrarily many such steps may surround one observable step. *)
val bind_ghost (#a:Type u#a) (#b:Type u#b)
  (#m1 #m2 #m3:inames) (#p:slprop) (#q:a -> slprop) (#r:b -> slprop)
  (f:gaction a m1 m2 p q)
  (g:(x:a -> gaction b m2 m3 (q x) r))
  : gaction b m1 m3 p r

(** Carry a spatial frame through a ghost mask transition without consuming it. *)
val frame_ghost (#a:Type u#a)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (r:slprop) (f:gaction a m1 m2 p q)
  : gaction a m1 m2 (p ** r) (fun x -> q x ** r)

(** Forget runtime availability of a neutral action and its result. The
`Neutral` index is essential: observable heap effects cannot be erased. *)
val action_to_ghost (#a:Type u#a)
  (#m1 #m2:inames) (#p:slprop) (#q:a -> slprop)
  (f:action a Neutral m1 m2 p q)
  : gaction a m1 m2 p q

(** Transport along equal assertions. This is not a general consequence rule:
callers must establish equality of the precondition and each postcondition. *)
val sub_ghost (#a:Type u#a) (#m1 #m2:inames)
  (#p:slprop) (#q:a -> slprop)
  (p':slprop { p == p' })
  (q':(a -> slprop) { forall x. q x == q' x })
  (f:gaction a m1 m2 p q)
  : gaction a m1 m2 p' q'

(** Transport along extensionally equal masks, e.g. after commuting two set
insertions for non-LIFO closing. It cannot discard an actually open name. *)
val reindex_ghost (#a:Type u#a) (#m1 #m2:inames)
  (#p:slprop) (#q:a -> slprop)
  (before:inames { before == m1 }) (after:inames { after == m2 })
  (f:gaction a m1 m2 p q)
  : gaction a before after p q

(** Run ghost cleanup, then return an already available runtime value. The
value is not computed from the erased result of the cleanup action. *)
inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#m1 #m2 #p:unit) (x:a) (_ _:unit) -> x))]
val finish_ghost (#a:Type u#a) (#m1 #m2:inames) (#p:slprop)
  (x:a) (post:a -> slprop) (f:gaction unit m1 m2 p (fun _ -> post x))
  : action a Neutral m1 m2 p post

(** Re-enter Pulse with a chosen footprint. The action must work for EVERY
ambient open mask disjoint from `opens`, and must restore that same mask.
This is the interface for deriving selective-footprint operations. *)
inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#o #p #q:unit) (_:unit) (f:unit -> Dv a) -> f ()))]
val run (#a:Type0) (#o:observability) (#p:slprop) (#q:a -> slprop)
  (opens:inames)
  (f:(mask:inames { mask /! opens } -> action a o mask mask p q))
  : stt_atomic a #o opens p q

(** Convenient runner for a closed-to-closed action. Its `all_inames` footprint
means it cannot be nested inside an already-open lexical invariant. It does
not mean that all invariant bodies are made available to the action. *)
inline_for_extraction
[@@extract_as (`(fun (#a:Type0) (#o #p #q:unit) (f:a) -> f))]
val run_closed (#a:Type0) (#o:observability) (#p:slprop) (#q:a -> slprop)
  (f:action a o emp_inames emp_inames p q)
  : stt_atomic a #o all_inames p q

(** Open a CORE invariant, exposing a localized, later-guarded body. This
does not eliminate `later` or locality; use Invariant.open_inv for the
ordinary Pulse.Lib.Inv API. Absence of `i` prevents double opening. *)
val open_invariant (mask:inames) (i:iname { not (mem_inv mask i) }) (p:slprop)
  : gaction unit mask (add_inv mask i)
      (I.inv i p)
      (fun _ -> I.inv i p ** I.somewhere (later p))

(** Restore the localized, later-guarded core body and remove `i` from the
open mask. Other open names need not be closed in stack order. *)
val close_invariant (mask:inames) (i:iname { not (mem_inv mask i) }) (p:slprop)
  : gaction unit (add_inv mask i) mask
      (I.inv i p ** I.somewhere (later p))
      (fun _ -> I.inv i p)
