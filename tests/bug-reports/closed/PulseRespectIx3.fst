module PulseRespectIx3

#lang-pulse
open Pulse

// Postcondition mismatch: impl promises emp but interface promises pure (1 == 2)
[@@expect_failure]
ghost
fn foo ()
  ensures emp
{ (); }

(* [foo] still has to be implemented, or the module is (rightly) rejected for
   not implementing its interface. There is no real implementation, of course. *)
ghost
fn foo ()
  ensures pure (1 == 2)
{
  admit()
}
