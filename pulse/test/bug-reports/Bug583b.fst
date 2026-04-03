module Bug583b
open Pulse
#lang-pulse
open Pulse.Lib.BoundedIntegers
module SZ = FStar.SizeT
module R  = Pulse.Lib.Reference

fn binary_search_style_FAILS
  (lo_init hi_init: SZ.t)
  requires pure (SZ.v lo_init < SZ.v hi_init /\ SZ.v hi_init <= 100)
  returns _: unit
  ensures pure True
{
  let mut lo: SZ.t = lo_init;
  let mut hi: SZ.t = hi_init;

  while (
    let vlo = !lo;
    let vhi = !hi;
    (vhi - vlo) > 1sz
  )
  invariant exists* vlo vhi.
    R.pts_to lo vlo **
    R.pts_to hi vhi **
    pure (
      SZ.v vlo <= SZ.v vhi /\
      SZ.v vhi <= 100
    )
  {
    let vlo = !lo;
    let vhi = !hi;
    let mid = vlo + ((vhi - vlo) / 2sz);
    lo := mid
  }
}