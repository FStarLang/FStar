module ProjAbbrev
#lang-pulse
open Pulse
module R = Pulse.Lib.Reference
module U32 = FStar.UInt32

let validator (a : Type0) =
  (r: R.ref a) -> (#p: perm) -> (#v: erased a) ->
  stt bool (R.pts_to r #p v) (fun _ -> R.pts_to r #p v)

noeq type box (a : Type0) = { v : validator a; tag : U32.t }

let getv (#a : Type0) (b : box a) : validator a = b.v

fn is_five (r: R.ref U32.t) (#p: perm) (#v: erased U32.t)
    requires R.pts_to r #p v
    returns  res:bool
    ensures  R.pts_to r #p v
{
  let x = !r;
  U32.(x =^ 5ul)
}

let mk (t : U32.t) : box U32.t = { v = is_five; tag = t }

fn run (b : box U32.t) (r : R.ref U32.t) (#p: perm) (#v: erased U32.t)
    requires R.pts_to r #p v
    returns  res:bool
    ensures  R.pts_to r #p v
{
  let f = getv b;
  f r
}

fn main ()
  returns c:FStar.SizeT.t
{
  let r = R.alloc 5ul;
  let b = mk 1ul;
  let ok = run b r;
  R.free r;
  if ok { 0sz } else { 1sz }
}
