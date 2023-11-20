module Pulse.Lib.Box

open Pulse.Lib.Core

module R = Pulse.Lib.Reference

type box a = R.ref a
let pts_to b #p v = R.pts_to b #p v
let alloc x = R.alloc x
let op_Bang b = R.op_Bang b 
let op_Colon_Equals b x = R.op_Colon_Equals b x
let free b = R.free b

let box_to_ref b = b

let to_ref_pts_to #a b #p #v =
  rewrite (pts_to b #p v) (R.pts_to b #p v) (vprop_equiv_refl _)

let to_box_pts_to #a r #p #v =
  rewrite (R.pts_to r #p v) (pts_to r #p v) (vprop_equiv_refl _)
