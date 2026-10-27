module Pulse.Lib.LogicalAtomicity.Invariant

(**
Separate opening and closing for ordinary Pulse.Lib.Inv invariants.

The existing invariant predicate, allocation API, locality discipline, and
later guard are unchanged. Only the proof interface is generalized: the open
mask in Masks.gaction tracks an outstanding body instead of a lexical block.
Thus multiple invariants may be closed in a different order than they opened.

This is analogous to invariant access through Iris mask-changing updates,
with reversed mask polarity and an explicit Pulse later credit. It is not
permission to retain an open body across arbitrary program steps: a runner
must balance masks and its action may contain at most one observable step.
*)

open Pulse.Lib.Core
open Pulse.Lib.Inv
module M = Pulse.Lib.LogicalAtomicity.Masks

(** Add i to the open mask and expose p in the caller's locality. Spend one
credit to remove the later guarding the invariant body. The persistent inv
handle remains available, but the mask forbids opening it a second time. *)
val open_inv (mask:inames) (i:iname { not (mem_inv mask i) }) (p:slprop)
  : M.gaction unit mask (add_inv mask i)
      (inv i p ** later_credit 1) (fun _ -> inv i p ** p)

(** Return p to its invariant and remove i from the mask. Closing introduces
later and therefore costs no new credit. The handle alone cannot close:
the entire body must be restored, even if other names remain open. *)
val close_inv (mask:inames) (i:iname { not (mem_inv mask i) }) (p:slprop)
  : M.gaction unit (add_inv mask i) mask
      (inv i p ** p) (fun _ -> inv i p)
