module Pulse.Lib.LogicalAtomicity.Update
#lang-pulse

(**
First-class, resource-capturing ghost updates.

`wand before after p q` packages ownership and a ghost program that, when
given `p`, produces `q` while changing the open mask. `fupd` is its emp-input
specialization. This plays the role of Iris's mask-changing fancy update
and update wand, but is a derived Pulse assertion, not a primitive modality
with all of Iris's laws. In particular, mask weakening, later interaction,
and arbitrary Iris proof-mode rules are not supplied by this interface.

The captured resources are spatial, not implicitly persistent or sendable.
Eliminating the package consumes it; merely owning it does not execute it.
See Masks for the reversed mask polarity and the single-observable-step
restriction when an update is composed with executable code.
*)

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks

(** An owned, one-use mask-changing implication. Captured state is hidden;
the caller must still supply `p` at elimination time. *)
val wand (before after:inames) (p q:slprop) : slprop

(** A suspended update yielding `p` without additional input ownership.
It may still own hidden resources and change the mask when eliminated. *)
let fupd (before after:inames) (p:slprop) = wand before after emp p

(** Capture `extra` with a reusable pure code witness. The witness receives
`extra ** p`; only ownership of `extra`, not the code, is consumed by packing. *)
ghost fn intro_wand (before after:inames) (p q extra:slprop)
  (k:unit -> M.gaction unit before after (extra ** p) (fun _ -> q))
  requires extra
  ensures wand before after p q

(** Consume the package and its input, run the hidden ghost program, and
obtain `q` at the output mask. There is no implicit duplicate continuation. *)
val elim_wand (before after:inames) (p q:slprop)
  : M.gaction unit before after (wand before after p q ** p) (fun _ -> q)

(** Suspend resources already owned as an equal-mask update; no invariant
is opened and no later credit is needed. *)
ghost fn return_update (mask:inames) (p:slprop)
  requires p
  ensures fupd mask mask p

(** Execute the emp-input specialization of elim_wand. *)
val elim_update (before after:inames) (p:slprop)
  : M.gaction unit before after (fupd before after p) (fun _ -> p)

(** Consume two update wands and package their sequential composition.
Both the intermediate mask and intermediate assertion must match. *)
ghost fn compose (m1 m2 m3:inames) (p q r:slprop)
  requires wand m1 m2 p q ** wand m2 m3 q r
  ensures wand m1 m3 p r

(** Adapt a wand to carry `r` untouched. The resource `r` is supplied at
elimination, not captured when constructing the framed wand. *)
ghost fn frame (m1 m2:inames) (p q r:slprop)
  requires wand m1 m2 p q
  ensures wand m1 m2 (p ** r) (q ** r)

(** Postcompose an update with an ordinary ghost transformation. Its empty
footprint makes it safe at any output mask; the mask transition is unchanged. *)
ghost fn map (m1 m2:inames) (p q:slprop)
  (k:unit -> stt_ghost unit emp_inames p (fun _ -> q))
  requires fupd m1 m2 p
  ensures fupd m1 m2 q
