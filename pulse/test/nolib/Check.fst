module Check

#lang-pulse
open Pulse.Nolib

ghost
fn test (x : int)
  requires pure (x == 'y)
  returns z : int
  ensures pure (z == x)
{
  x
}

#check test
