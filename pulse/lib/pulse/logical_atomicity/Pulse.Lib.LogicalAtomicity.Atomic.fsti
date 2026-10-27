module Pulse.Lib.LogicalAtomicity.Atomic
#lang-pulse

(**
Atomic accessors and retryable atomic updates (AU).

An implementation opens an AU to observe some abstract state `x` and own
`alpha x`. A failed attempt restores that same resource and aborts; a
linearizing attempt establishes `beta x y` and commits to `phi x y`. Between
attempts the state can change: the next opening may expose a different `x`.
Only the selected closing branch owns the captured client continuation.

This follows the abort/commit structure of Iris's `atomic_acc` and
`atomic_update` (iris.bi.lib.atomic; linked in README.md). The reusable AU is
encoded here by an existential state and a step witness whose abort restores
that state, rather than by adding a primitive recursive spatial predicate.
No equivalence with Iris's greatest-fixed-point definition is claimed.

The combinators express the client/implementation handshake underlying a
logically atomic specification in the sense of TaDA. They do not themselves
prove that a multi-step program implements a particular abstract operation:
the implementation must connect beta to its actual linearizing step. Credits,
sendability, and progress remain explicit obligations. These are safety and
partial-correctness rules, not termination or lock-freedom rules.
*)

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module U = Pulse.Lib.LogicalAtomicity.Update

(** One ADDITIVE choice: None selects abort, Some y selects commit.
`forall*` lets either branch use the same captured resource; it is not two
separately owned wands. This prevents committing twice or aborting afterward. *)
let closing (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (abort:slprop) (beta phi:a -> b -> slprop) (x:a) =
  forall* (decision:option b).
    U.wand inner outer
      (match decision with | None -> alpha x | Some y -> beta x y)
      (match decision with | None -> abort | Some y -> phi x y)

(** The state exposed at this attempt together with its one-use closing
choice. The existential state is chosen on opening, not fixed at call entry. *)
let opened (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (abort:slprop) (beta phi:a -> b -> slprop) =
  exists* x. alpha x ** closing outer inner alpha abort beta phi x

(** One suspended opening with a caller-selected abort resource. Unlike an
AU, a general accessor need not restore itself when aborted. *)
let accessor (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (abort:slprop) (beta phi:a -> b -> slprop) =
  U.fupd outer inner (opened outer inner alpha abort beta phi)

(** Capture `extra` once and prove both alternative closing programs against
it. Both restore the outer mask; abort needs alpha, commit needs beta. *)
ghost fn intro_closing (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (abort:slprop) (beta phi:a -> b -> slprop)
  (x:a) (extra:slprop)
  (on_abort:unit -> M.gaction unit inner outer (extra ** alpha x) (fun _ -> abort))
  (on_commit:(y:b -> M.gaction unit inner outer (extra ** beta x y) (fun _ -> phi x y)))
  requires extra
  ensures closing outer inner alpha abort beta phi x

(** Choose abort, returning `retry` after restoring the observed alpha.
This does not roll back physical writes or refund spent later credits. *)
val abort (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (retry:slprop) (beta phi:a -> b -> slprop) (x:a)
  : M.gaction unit inner outer
      (closing outer inner alpha retry beta phi x ** alpha x) (fun _ -> retry)

(** Choose commit once beta has been established at the linearization point.
Consumes the closing capability and produces the client's phi; no retry
capability is returned unless phi explicitly contains one. *)
val commit (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (retry:slprop) (beta phi:a -> b -> slprop) (x:a) (y:b)
  : M.gaction unit inner outer
      (closing outer inner alpha retry beta phi x ** beta x y) (fun _ -> phi x y)

(** An owned capability supporting repeated open/abort attempts and a
consuming commit. `credits` is the cost of EACH opening, not a retry bound.
Hidden captured ownership need not be duplicable or transferable to threads. *)
val atomic_update (#a #b:Type0) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) : slprop

(** Supply an invariant for the retry protocol: hidden `state` and code that
opens it, with abort returning state. Repackaging state with the same code
gives unbounded retry capability without recursively defining an slprop. *)
ghost fn intro (#a #b:Type0) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) (state:slprop)
  (step:unit -> M.gaction unit outer inner (state ** later_credit credits)
    (fun _ -> opened outer inner alpha state beta phi))
  requires state
  ensures atomic_update outer inner credits alpha beta phi

(** Spend fresh opening credits and expose alpha with a closing choice whose
abort restores the AU itself. This is the reusable accessor elimination rule. *)
val open_update (#a #b:Type0) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  : M.gaction unit outer inner
      (atomic_update outer inner credits alpha beta phi ** later_credit credits)
      (fun _ -> opened outer inner alpha (atomic_update outer inner credits alpha beta phi) beta phi)

(** Abort without inspecting the existential state. Useful for speculative
reads and failed CAS paths that leave alpha unchanged. *)
val abort_opened (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (retry:slprop) (beta phi:a -> b -> slprop)
  : M.gaction unit inner outer (opened outer inner alpha retry beta phi) (fun _ -> retry)
