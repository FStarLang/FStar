module Bug347b
#lang-pulse
open Pulse

assume
val foo : unit -> stt int (requires emp) (ensures fun x -> pure (x == 1))

[@@expect_failure] // should work
fn test ()
  requires emp
  returns  x : (x:int{x == 1})
  ensures  emp
{
   foo ();
}
