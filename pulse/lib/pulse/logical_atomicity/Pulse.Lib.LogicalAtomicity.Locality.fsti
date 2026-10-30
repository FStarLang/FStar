module Pulse.Lib.LogicalAtomicity.Locality
#lang-pulse

(**
Caller-local atomic updates for ghost helping.

An AU can capture non-sendable resources, so a helper cannot simply move the
AU to its own locality. Instead it owns `on l AU`: the AU, its hidden state,
and its closing continuation stay anchored to the initiating caller `l`.
`Masks.localize` executes the ghost protocol there and restores the helper's
locality afterward, including when opening and closing change the mask.

Only the abstract resources exchanged with the helper must be placeless:
alpha when opening or aborting, beta when committing. Neither captured client
ownership nor phi needs a sendability or duplicability instance. These rules
do not authorize physical operations at another thread's locality, duplicate
a closing capability, or provide a progress theorem.
*)

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module A = Pulse.Lib.LogicalAtomicity.Atomic

(** The helper owns alpha at its own locality, but the additive abort/commit
choice remains at `l`. Exposing this definition lets the implementation
inspect the abstract state and establish beta without moving client state. *)
let opened (#a #b:Type0) (l:loc_id) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) =
  exists* x. alpha x **
    on l (A.closing outer inner alpha
      (A.atomic_update outer inner credits alpha beta phi) beta phi x)

(** Spend this opening's credits, run the caller's accessor, and move only
placeless alpha out of `on l`. The helper is left at the inner mask. *)
val open_update (#a #b:Type0) (l:loc_id) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  {| pa: (x:a -> placeless (alpha x)) |}
  : M.gaction unit outer inner
      (on l (A.atomic_update outer inner credits alpha beta phi) ** later_credit credits)
      (fun _ -> opened l outer inner credits alpha beta phi)

(** Return established beta to `l`, consume the one-use commitment, and
restore the outer mask. The resulting phi stays anchored to the caller. *)
val commit (#a #b:Type0) (l:loc_id) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) (x:a) (y:b)
  {| pb: placeless (beta x y) |}
  : M.gaction unit inner outer
      (on l (A.closing outer inner alpha
        (A.atomic_update outer inner credits alpha beta phi) beta phi x) ** beta x y)
      (fun _ -> on l (phi x y))

(** Return the unchanged alpha to `l` and abort, recovering the caller-local
AU at the outer mask. Spent opening credits are not refunded. *)
val abort (#a #b:Type0) (l:loc_id) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  {| pa: (x:a -> placeless (alpha x)) |}
  : M.gaction unit inner outer (opened l outer inner credits alpha beta phi)
      (fun _ -> on l (A.atomic_update outer inner credits alpha beta phi))
