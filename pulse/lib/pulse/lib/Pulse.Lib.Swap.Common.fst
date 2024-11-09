module Pulse.Lib.Swap.Common
#lang-pulse
open Pulse.Lib.Pervasives
module Prf = Pulse.Lib.Swap.Spec
module SZ = FStar.SizeT

#set-options "--fuel 2 --ifuel 1"
#restart-solver

inline_for_extraction
fn gcd (n0: SZ.t) (l0: SZ.t)
  requires (emp ** pure (
    SZ.v l0 < SZ.v n0
  ))
  returns res : SZ.t
  ensures (emp ** pure (
    SZ.v l0 < SZ.v n0 /\
    SZ.v res == (Prf.mk_bezout (SZ.v n0) (SZ.v l0)).d  
  ))
{
  let mut pn = n0;
  let mut pl = l0;
  while (let l = !pl ; (l `SZ.gt` 0sz))
  invariant b . exists* n l . (
    pts_to pn n **
    pts_to pl l **
    pure (
      SZ.v l < SZ.v n /\
      (Prf.mk_bezout (SZ.v n0) (SZ.v l0)).d == (Prf.mk_bezout (SZ.v n) (SZ.v l)).d /\
      b == (SZ.v l > 0)
    ))
  {
    let n = !pn;
    let l = !pl;
    let l' = SZ.rem n l;
    pn := l;
    pl := l';
    ()
  };
  let res = !pn;
  res
}

inline_for_extraction
let impl_jump
  (lb rb mb: SZ.t)
  (idx: SZ.t)
  (_: squash (
      SZ.v lb < SZ.v mb /\
      SZ.v mb < SZ.v rb /\
      SZ.v lb <= SZ.v idx /\
      SZ.v idx < SZ.v rb
  ))
: Tot (idx': SZ.t {
      SZ.v idx' == SZ.v lb + Prf.jump (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) (SZ.v idx - SZ.v lb)
  })
= Prf.jump_if (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) () (SZ.v idx - SZ.v lb);
  [@@inline_let]
  let nl = rb `SZ.sub` mb in
  if (idx `SZ.sub` lb) `SZ.gte` nl
  then idx `SZ.sub` nl
  else idx `SZ.add` (mb `SZ.sub` lb)
