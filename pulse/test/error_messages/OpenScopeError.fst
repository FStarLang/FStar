module OpenScopeError
#lang-pulse
open Pulse.Lib.Pervasives

// Opening a nonexistent module should produce a localized error
[@@expect_failure [168]]
fn open_fail ()
  requires emp
  ensures emp
{
  open NonExistent.Module;
  ()
}
