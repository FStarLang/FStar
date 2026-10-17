module Pulse.Lib.Sleep
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main

(* Model implementation of Pulse.Lib.Sleep: verified, but never extracted.
   Sleeping has no observable effect on the heap. *)
fn sleep_ms (msecs : int)
{
  ()
}
