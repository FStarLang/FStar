module IfacePulseCircular

(* Issue #4390, in a language extension. The interface of this module declares

     ghost fn bad () requires emp ensures pure False

   and then *defines*

     ghost fn derived () requires emp ensures pure False { bad (); }

   If [derived] were in scope here, this implementation would discharge [bad]
   with it and the module would hand out a ghost proof of [False]. [derived]
   must stay hidden until [bad] has been implemented. *)

#lang-pulse
open Pulse

ghost
fn bad ()
  requires emp
  ensures pure False
{
  derived ();
}
