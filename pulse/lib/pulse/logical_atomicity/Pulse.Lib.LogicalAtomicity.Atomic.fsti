module Pulse.Lib.LogicalAtomicity.Atomic
#lang-pulse

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module U = Pulse.Lib.LogicalAtomicity.Update

// The universal quantifier is additive: either branch uses the same resource.
let closing (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (abort:slprop) (beta phi:a -> b -> slprop) (x:a) =
  forall* (decision:option b).
    U.wand inner outer
      (match decision with | None -> alpha x | Some y -> beta x y)
      (match decision with | None -> abort | Some y -> phi x y)

let opened (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (abort:slprop) (beta phi:a -> b -> slprop) =
  exists* x. alpha x ** closing outer inner alpha abort beta phi x

let accessor (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (abort:slprop) (beta phi:a -> b -> slprop) =
  U.fupd outer inner (opened outer inner alpha abort beta phi)

ghost fn intro_closing (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (abort:slprop) (beta phi:a -> b -> slprop)
  (x:a) (extra:slprop)
  (on_abort:unit -> M.gaction unit inner outer (extra ** alpha x) (fun _ -> abort))
  (on_commit:(y:b -> M.gaction unit inner outer (extra ** beta x y) (fun _ -> phi x y)))
  requires extra
  ensures closing outer inner alpha abort beta phi x

val abort (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (retry:slprop) (beta phi:a -> b -> slprop) (x:a)
  : M.gaction unit inner outer
      (closing outer inner alpha retry beta phi x ** alpha x) (fun _ -> retry)

val commit (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (retry:slprop) (beta phi:a -> b -> slprop) (x:a) (y:b)
  : M.gaction unit inner outer
      (closing outer inner alpha retry beta phi x ** beta x y) (fun _ -> phi x y)

val atomic_update (#a #b:Type0) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) : slprop

// A coinduction witness: abort restores state, so the same step can run again.
ghost fn intro (#a #b:Type0) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop) (state:slprop)
  (step:unit -> M.gaction unit outer inner (state ** later_credit credits)
    (fun _ -> opened outer inner alpha state beta phi))
  requires state
  ensures atomic_update outer inner credits alpha beta phi

// Each attempt supplies fresh later credits; abort does not refund them.
val open_update (#a #b:Type0) (outer inner:inames) (credits:nat)
  (alpha:a -> slprop) (beta phi:a -> b -> slprop)
  : M.gaction unit outer inner
      (atomic_update outer inner credits alpha beta phi ** later_credit credits)
      (fun _ -> opened outer inner alpha (atomic_update outer inner credits alpha beta phi) beta phi)

val abort_opened (#a #b:Type0) (outer inner:inames)
  (alpha:a -> slprop) (retry:slprop) (beta phi:a -> b -> slprop)
  : M.gaction unit inner outer (opened outer inner alpha retry beta phi) (fun _ -> retry)
