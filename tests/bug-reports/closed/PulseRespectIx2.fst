module PulseRespectIx2

#lang-pulse
open Pulse

[@@expect_failure]
ghost
fn foo (x:False)
  ensures pure False
{
  ();
}
