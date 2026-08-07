module IfacePulseSkipCircular

(* Issue #4390 again, this time reached by implementing the interface out of
   order. [other] is implemented first, leaving [bad] outstanding; if that were
   allowed, the interface definition of [derived] -- which is justified by
   [bad] -- would come into scope and could be used below to discharge [bad]
   itself, yielding a ghost proof of [False].

   A declaration introduced by a language extension is no different from a
   plain [val]: it must be implemented in the position the interface gives it,
   so the very first definition below is rejected. *)

#lang-pulse
open Pulse

ghost
fn other ()
  requires emp
  ensures emp
{ (); }

#lang-pulse
open Pulse

ghost
fn bad ()
  requires emp
  ensures pure False
{
  derived ();
}
