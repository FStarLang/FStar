module DuplicateResource
#lang-pulse
open Pulse.Lib.Pervasives

// Trying to read a ref twice without proper framing
[@@expect_failure [228]]
fn dup_fail (r: ref int)
  requires pts_to r 0
  ensures pts_to r 0 ** pts_to r 0
{
  ()
}
