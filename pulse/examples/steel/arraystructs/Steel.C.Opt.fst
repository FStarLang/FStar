module Steel.C.Opt

open Steel.C.PCM
module A = Steel.Effect.Atomic

let opt_read r =
  let Some x = ref_read r in
  x

let opt_write #a #b #x r y =
  ref_upd r (Some (Ghost.reveal x)) (Some y) (fun (Some _) -> Some y);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _)

let opt_pcm_write
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b)) (y: b)
: Steel unit (r `pts_to` x) (fun _ -> r `pts_to` Some y)
  (requires (fun _ -> Some? x))
  (ensures (fun _ _ _ -> True))
= ref_upd r x (Some y) (opt_pcm_fpu x y)

let opt_pcm_read
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b))
: Steel b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (fun _ -> Some? x))
  (ensures (fun _ y _ -> Ghost.reveal x == Some y))
= let y' = ref_read r in
  assert (Ghost.reveal x == y');
  Some?.v y'
