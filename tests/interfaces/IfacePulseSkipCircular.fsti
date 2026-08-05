module IfacePulseSkipCircular

(* Interface declarations produced by a language extension used to be
   matchable by name rather than by position: the implementation could skip
   past [bad] and implement [other] first. Doing so revealed [derived], which
   is justified by [bad] -- see IfacePulseSkipCircular.fst. *)

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

#lang-pulse
open Pulse

ghost
fn other ()
  requires emp
  ensures emp
