module Steel.C.Opt
include Steel.ST.C.Opt

module P = FStar.PCM
open Steel.C.Model.PCM
open Steel.C.Model.Ref
open Steel.Effect

let opt_view
  (a: Type)
: Tot (sel_view (opt_pcm #a) a false)
= {
  to_view_prop = (fun x -> Some? x == true);
  to_view = (fun x -> Some?.v x);
  to_carrier = (fun z  -> Some z);
  to_carrier_not_one = ();
  to_view_frame = (fun x frame -> ());
}

val opt_read_sel
  (#a: Type u#0) (#b: Type u#0)
  (r: ref a (opt_pcm #b))
: Steel b
  (pts_to_view r (opt_view b))
  (fun _ -> pts_to_view r (opt_view b))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    res == h (pts_to_view r (opt_view b)) /\
    res == h' (pts_to_view r (opt_view b))
  ))

val opt_write_sel
  (#a: Type u#0) (#b: Type u#0)
  (r: ref a (opt_pcm #b))
  (w: b)
: Steel unit
  (pts_to_view r (opt_view b))
  (fun _ -> pts_to_view r (opt_view b))
  (requires (fun _ -> True))
  (ensures (fun _ _ h' ->
    w == h' (pts_to_view r (opt_view b))
  ))

open Steel.C.Reference

val ref_opt_read
  (#a: Type u#0) (#b: Type u#0)
  (r: ref a b (opt_pcm #b))
: Steel b
  (pts_to_view r (opt_view b))
  (fun _ -> pts_to_view r (opt_view b))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    res == h (pts_to_view r (opt_view b)) /\
    res == h' (pts_to_view r (opt_view b))
  ))

val ref_opt_write
  (#a: Type u#0) (#b: Type u#0)
  (r: ref a b (opt_pcm #b))
  (w: b)
: Steel unit
  (pts_to_view r (opt_view b))
  (fun _ -> pts_to_view r (opt_view b))
  (requires (fun _ -> True))
  (ensures (fun _ _ h' ->
    w == h' (pts_to_view r (opt_view b))
  ))

val malloc
  (#c:Type0) (x: c)
: Steel (ptr (option c) c (opt_pcm #c))
    emp
    (fun r -> pts_to_view_or_null r (opt_view c))
    (requires fun _ -> True)
    (ensures fun _ r h' ->
      let s = h' (pts_to_view_or_null r (opt_view c)) in
      ptr_is_null r == None? s /\
      (Some? s ==> (Some?.v s == x /\ freeable r))
    )

val free
  (#c: Type0)
  (r: ref (option c) c (opt_pcm #c))
: Steel unit
    (pts_to_view r (opt_view c))
    (fun _ -> emp)
    (requires fun _ -> freeable r)
    (ensures fun _ _ _ -> True)
