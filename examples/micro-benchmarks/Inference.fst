module Inference

open FStar.HyperStack
open FStar.HyperStack.ST
module MDM = FStar.Monotonic.DependentMap

// a should be inferred as an `eqtype`
let alloc #a #b #inv (r: erid):
  ST (MDM.t r a b inv)
    (requires (fun h ->
      inv (MDM.empty_partial_dependent_map #a #b) /\
      witnessed (region_contains_pred r) ))
    (ensures (fun h0 x h1 ->
      inv (MDM.empty_partial_dependent_map #a #b) /\
      ralloc_post r (MDM.empty #a #b) h0 x h1))
  = MDM.alloc #a #b #inv #r ()
