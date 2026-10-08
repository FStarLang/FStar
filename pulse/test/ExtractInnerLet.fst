module ExtractInnerLet
#lang-pulse
open Pulse
module SZ = FStar.SizeT

(* Phase 1 leaves the type of an unannotated inner let in a pure Pulse
   expression as [_]; extraction must recover it. *)

let lte_plain (a b:SZ.t) : bool = SZ.lte a b

fn inner_let (x:SZ.t)
  returns b:bool
{
  let r = (let y = SZ.add x 0sz in lte_plain y 5sz);
  r
}

fn inner_let_in_branch (x:SZ.t)
  returns b:bool
{
  let r = (
    if SZ.lte 1sz x then
      let y = SZ.sub x 1sz in
      lte_plain y 5sz
    else
      false);
  r
}
