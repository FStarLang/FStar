module MissingPost
#lang-pulse
open Pulse.Lib.Pervasives

// Function allocates but doesn't return it in post
[@@expect_failure [228]]
fn missing_post (r: ref int)
  requires pts_to r 0
  ensures emp
{
  r := 1;
  ()  // ERROR: pts_to r 1 is leftover, post says emp
}
