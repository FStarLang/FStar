module PulseRespectIx4

#lang-pulse
open Pulse

// Swapped order: bar defined before foo.
// Interface checking should match by name, not position.

ghost
fn bar ()
  ensures emp
{ (); }

#lang-pulse
open Pulse

[@@expect_failure]
ghost
fn foo ()
  requires pure False
  ensures pure False
{ (); }
(* [foo] still has to be implemented, or the module is (rightly) rejected for
   not implementing its interface. There is no real implementation, of course. *)
ghost
fn foo ()
  ensures pure False
{
  admit()
}
