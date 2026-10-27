module Pulse.Lib.LogicalAtomicity.Update
#lang-pulse

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks

let runner before after p q extra =
  unit -> M.gaction unit before after (extra ** p) (fun _ -> q)

let runner_exists before after p q extra =
  pure (nonempty (runner before after p q extra))

let wand (before after:inames) (p q:slprop) =
  exists* extra. extra ** runner_exists before after p q extra

ghost fn intro_wand (before after:inames) (p q extra:slprop)
  (k:unit -> M.gaction unit before after (extra ** p) (fun _ -> q))
  requires extra
  ensures wand before after p q
{
  nonempty_intro (k <: runner before after p q extra);
  fold runner_exists before after p q extra;
  fold wand before after p q;
}

private ghost fn unpack (before after:inames) (p q:slprop)
  requires wand before after p q
  returns res:(extra:erased slprop & runner before after p q extra)
  ensures dfst res
{
  unfold wand before after p q;
  with extra. _;
  unfold runner_exists before after p q extra;
  let k = nonempty_elim (runner before after p q extra);
  (| (extra <: erased slprop), k |)
}

let elim_wand before after p q
  : M.gaction unit before after (wand before after p q ** p) (fun _ -> q) =
  M.bind_ghost
    (M.lift_ghost before (Pulse.Lib.Core.frame_ghost p (unpack before after p q)))
    (fun res -> (dsnd res) ())

ghost fn return_update (mask:inames) (p:slprop)
  requires p
  ensures fupd mask mask p
{
  ghost fn identity () requires p ** emp ensures p {};
  star_comm p emp;
  emp_unit p;
  intro_wand mask mask emp p p (fun _ -> M.lift_ghost mask (identity ()));
  fold fupd mask mask p;
}

let elim_update before after p
  : M.gaction unit before after (fupd before after p) (fun _ -> p) =
  star_comm (fupd before after p) emp;
  emp_unit (fupd before after p);
  elim_wand before after emp p

ghost fn compose (m1 m2 m3:inames) (p q r:slprop)
  requires wand m1 m2 p q ** wand m2 m3 q r
  ensures wand m1 m3 p r
{
  let f = unpack m1 m2 p q;
  let g = unpack m2 m3 q r;
  slprop_equivs ();
  rewrite each dfst f as f._1;
  rewrite each dfst g as g._1;
  intro_wand m1 m3 p r (dfst f ** dfst g) (fun _ ->
    star_assoc (dfst f) (dfst g) p;
    star_comm (dfst g) p;
    M.bind_ghost
      (M.frame_ghost (dfst g) ((dsnd f) ()))
      (fun _ ->
        star_comm q (dfst g);
        (dsnd g) ()));
}

ghost fn frame (m1 m2:inames) (p q r:slprop)
  requires wand m1 m2 p q
  ensures wand m1 m2 (p ** r) (q ** r)
{
  let f = unpack m1 m2 p q;
  slprop_equivs ();
  rewrite each dfst f as f._1;
  intro_wand m1 m2 (p ** r) (q ** r) (dfst f) (fun _ ->
    star_assoc (dfst f) p r;
    M.frame_ghost r ((dsnd f) ()));
}

ghost fn map (m1 m2:inames) (p q:slprop)
  (k:unit -> stt_ghost unit emp_inames p (fun _ -> q))
  requires fupd m1 m2 p
  ensures fupd m1 m2 q
{
  unfold fupd m1 m2 p;
  emp_unit p;
  intro_wand m2 m2 p q emp (fun _ ->
    M.lift_ghost m2 (k ()));
  compose m1 m2 m2 emp p q;
  fold fupd m1 m2 q;
}
