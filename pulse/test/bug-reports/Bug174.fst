module Bug174

#lang-pulse

open Pulse
open FStar.SizeT

[@@expect_failure]
fn bad_range
  (#tt : Type0)
  (r : ref tt)
  (#v : erased tt)
  preserves Pulse.Lib.Reference.pts_to r v
{
  let v = Pulse.Lib.Reference.op_Bang #t r;
  admit();
}
