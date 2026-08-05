module IfacePulseOrder

(* Declarations introduced by a language extension are subject to the same
   ordering discipline as plain `val`s: they must be implemented in the order
   the interface declares them. See IfaceWrongOrder for the `val` counterpart. *)

#lang-pulse
open Pulse

ghost
fn f ()
  ensures emp

#lang-pulse
open Pulse

ghost
fn g ()
  ensures emp
