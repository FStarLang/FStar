module Steel.C.Opt

open Steel.C.Model.PCM
module A = Steel.Effect.Atomic

let opt_read r =
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  let Some x = ref_read r in
  x

let opt_write #b #x r y =
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  ref_upd r (Some (Ghost.reveal x)) (Some y) (fun (Some _) -> Some y);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _)

let opt_pcm_write
  (#b: Type)
  (r: ref (opt_pcm #b)) (x: Ghost.erased (option b)) (y: b)
: Steel unit (r `pts_to` x) (fun _ -> r `pts_to` Some y)
  (requires (fun _ -> Some? x))
  (ensures (fun _ _ _ -> True))
= A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  ref_upd r x (Some y) (opt_pcm_fpu x y);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _)

let opt_pcm_read
  (#b: Type)
  (r: ref (opt_pcm #b)) (x: Ghost.erased (option b))
: Steel b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (fun _ -> Some? x))
  (ensures (fun _ y _ -> Ghost.reveal x == Some y))
= A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  let y' = ref_read r in
  assert (Ghost.reveal x == y');
  Some?.v y'

let malloc
  #c x
=
  let xc = ((opt_view c).to_carrier x) in
  let r = Steel.C.Model.Ref.ref_alloc _ xc in
  pts_to_view_intro r xc (opt_view c) x;
  let r' : ref c (opt_pcm #c) = r in
  A.change_equal_slprop
    (Steel.C.Model.Ref.pts_to_view r (opt_view c))
    (pts_to_view r' (opt_view c));
  intro_pts_to_view_or_null_not_null r' (opt_view c);
  A.return r'

let free
  #c r
=
  let r' : Steel.C.Model.Ref.ref (opt_pcm #c) = r in 
  let _ = pts_to_view_elim r (opt_view c) in
  Steel.C.Model.Ref.ref_free r
