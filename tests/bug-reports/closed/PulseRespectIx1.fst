module PulseRespectIx1

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
