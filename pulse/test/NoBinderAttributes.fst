module NoBinderAttributes

#lang-pulse
open Pulse

[@@expect_failure]
fn test ()
{
  let [@@@123] x = 1;
  ();
}
