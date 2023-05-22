module Steel.C.Opt

open Steel.C.Model.PCM
module A = Steel.Effect.Atomic
module STC = Steel.ST.Coercions


let opt_read_sel
  #a #b r
= ref_read_sel r (opt_view b)

let opt_write_sel
  #a #b r w
=
  let _ = pts_to_view_elim r (opt_view _) in
  opt_pcm_write r _ w;
  pts_to_view_intro r _ (opt_view _) w

let ref_opt_read
  #a #b r
= ref_read_sel r (opt_view b)

let ref_opt_write
  #a #b r w
= opt_write_sel r w

let malloc
  #c x
=
  let xc = ((opt_view c).to_carrier x) in
  let r = Steel.C.Model.Ref.ref_alloc _ xc in
  pts_to_view_intro r xc (opt_view c) x;
  let r' : ref (option c) c (opt_pcm #c) = r in
  A.change_equal_slprop
    (Steel.C.Model.Ref.pts_to_view r (opt_view c))
    (pts_to_view r' (opt_view c));
  intro_pts_to_view_or_null_not_null r' (opt_view c);
  A.return r'

let free
  #c r
=
  let r' : Steel.C.Model.Ref.ref (option c) (opt_pcm #c) = r in 
  let _ = pts_to_view_elim r (opt_view c) in
  Steel.C.Model.Ref.ref_free r
