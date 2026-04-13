module PulseRespectIx2

#lang-pulse
open Pulse

[@@expect_failure]
ghost
fn foo (x:squash False)
  ensures pure False
{
  ();
}
