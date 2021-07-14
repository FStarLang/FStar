module FStar.PCM.POD

open Steel.C.PCM
module A = Steel.Effect.Atomic

let pod_read r =
  let Some x = ref_read r in
  x

let pod_write #a #b #x r y =
  ref_upd r (Some (Ghost.reveal x)) (Some y) (fun (Some _) -> Some y);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _)
