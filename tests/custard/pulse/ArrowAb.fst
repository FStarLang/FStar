module ArrowAb
#lang-pulse
open Pulse.Lib.Pervasives

(* Section 80.1.  The field's type is an arrow of arity 3, two of whose
   binders Custard erases.  F* stores the projector for such a field
   eta-expanded to the arrow's arity, so its body applies the projected value
   to the erased binders too -- and those are exactly the binders the
   projector itself no longer has. *)
noeq
type rec_t = {
  fld: (r: ref bool) -> (c: bool) -> (#p: perm) -> (#v: Ghost.erased bool) ->
       stt bool (pts_to r #p v) (fun _ -> pts_to r #p v);
}

fn impl (r: ref bool) (c: bool) (#p: perm) (#v: Ghost.erased bool)
  requires pts_to r #p v
  returns b: bool
  ensures pts_to r #p v
{
  let y = !r;
  c && y
}

fn call_it (t: rec_t) (r: ref bool) (x: bool) (#p: perm) (#v: Ghost.erased bool)
  requires pts_to r #p v
  returns b: bool
  ensures pts_to r #p v
{
  let f = t.fld;
  let b = f r x;
  b
}

fn main ()
  returns c: FStar.SizeT.t
{
  let mut r = true;
  let t = Mkrec_t impl;
  let ok = call_it t r true;
  if ok { 0sz } else { 1sz }
}
