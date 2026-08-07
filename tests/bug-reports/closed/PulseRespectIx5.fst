module PulseRespectIx5

#lang-pulse
open Pulse

// Non-ghost fn with precondition mismatch
[@@expect_failure]
fn foo ()
  requires pure False
  ensures pure False
{ (); }

(* [foo] still has to be implemented, or the module is (rightly) rejected for
   not implementing its interface. There is no real implementation, of course. *)
fn foo ()
  ensures pure False
{
  admit()
}
