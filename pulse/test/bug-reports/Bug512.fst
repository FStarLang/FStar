module Bug512

#lang-pulse
open Pulse
module SZ = FStar.SizeT

fn test (x y : SZ.t)
  requires pure (SZ.fits (SZ.v x + SZ.v y + 1))
{
  open FStar.SizeT;
  let mut z = x +^ y;
  z := !z +^ 1sz;
}

fn test2 (x y : SZ.t)
  requires pure (SZ.fits (SZ.v x + SZ.v y + 1))
{
  open FStar.SizeT;
  let z = x +^ y;
  // NB: z has a refined type, but w does not inherit
  // the refinement
  let mut w = z;
  w := !w +^ 1sz;
}
