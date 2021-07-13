module FStar.PCM.POD

open AggregateRef
module A = Steel.Effect.Atomic

let pod a = option a

let none #a = None #a
let some x = Some (Ghost.reveal x)

let pod_pcm a = FStar.PCM.Extras.opt_pcm #a

let pod_read r =
  let Some x = ref_read r in
  x

let pod_write r y =
  ref_write r (Some y);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _)
