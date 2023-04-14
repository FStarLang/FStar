module Steel.C.Model.Frac
include Steel.ST.C.Model.Frac

module STC = Steel.ST.Coercions // to use frac_pcm_write
module P = FStar.PCM
open Steel.C.Model.PCM
open Steel.C.Model.Ref
open Steel.Effect
open Steel.FractionalPermission

let frac_view
  (a: Type)
  (p: perm)
: Tot (sel_view (pcm_frac #a) a false)
= {
  to_view_prop = (fun x -> Some? x == true);
  to_view = (fun x -> let Some (v, _) = x in v);
  to_carrier = (fun v -> Some (v, p));
  to_carrier_not_one = ();
  to_view_frame = (fun v frame -> ());
}

let frac_read_sel
  (#a: Type u#0) (#b: Type u#0)
  (#p: perm)
  (r: ref a (pcm_frac #b))
: Steel b
  (pts_to_view r (frac_view _ p))
  (fun _ -> pts_to_view r (frac_view _ p))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    res == h (pts_to_view r (frac_view _ p)) /\
    res == h' (pts_to_view r (frac_view _ p))
  ))
= ref_read_sel r (frac_view _ p)

let frac_write_sel
  (#a: Type u#0) (#b: Type u#0)
  (#p: perm)
  (r: ref a (pcm_frac #b))
  (w: b)
: Steel unit
  (pts_to_view r (frac_view _ p))
  (fun _ -> pts_to_view r (frac_view _ p))
  (requires (fun _ -> p == full_perm))
  (ensures (fun h _ h' ->
    w == h' (pts_to_view r (frac_view _ p))
  ))
=
  let _ = pts_to_view_elim r (frac_view _ _) in
  frac_pcm_write r _ w;
  pts_to_view_intro r _ (frac_view _ p) w

