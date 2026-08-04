module IfacePulseCircular

(* The Pulse counterpart of IfaceCircular: [derived] is justified by the very
   declaration of [bad] that the implementation still has to discharge. *)

#lang-pulse
open Pulse

ghost
fn bad ()
  requires emp
  ensures pure False

#lang-pulse
open Pulse

ghost
fn derived ()
  requires emp
  ensures pure False
{
  bad ();
}
