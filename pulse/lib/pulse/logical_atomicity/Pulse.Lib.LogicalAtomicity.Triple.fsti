module Pulse.Lib.LogicalAtomicity.Triple
#lang-pulse

open Pulse.Lib.Pervasives
module A = Pulse.Lib.LogicalAtomicity.Atomic

let payload (#a:Type0) (alpha residual:a -> slprop) =
  exists* x. alpha x ** residual x

ghost fn from_invariant (#a #b:Type0)
  (outer:inames) (i:iname { not (mem_inv outer i) })
  (alpha residual:a -> slprop) (beta phi:a -> b -> slprop) (extra:slprop)
  (finish:(x:a -> y:b -> unit ->
    stt_ghost unit emp_inames (extra ** residual x ** beta x y)
      (fun _ -> payload alpha residual ** phi x y)))
  requires inv i (payload alpha residual) ** extra
  ensures A.atomic_update outer (add_inv outer i) 1 alpha beta phi
