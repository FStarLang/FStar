module Pulse.Lib.LogicalAtomicity.Invariant
open Pulse.Lib.Core
open Pulse.Lib.Inv
module M = Pulse.Lib.LogicalAtomicity.Masks

val open_inv (mask:inames) (i:iname { not (mem_inv mask i) }) (p:slprop)
  : M.gaction unit mask (add_inv mask i)
      (inv i p ** later_credit 1) (fun _ -> inv i p ** p)

val close_inv (mask:inames) (i:iname { not (mem_inv mask i) }) (p:slprop)
  : M.gaction unit (add_inv mask i) mask
      (inv i p ** p) (fun _ -> inv i p)
