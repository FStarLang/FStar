module GhostArgToSTCall
#lang-pulse
open Pulse

(* Passing an erased argument to a stateful function makes the application
   ghost, which Pulse.Checker.ST must reject.  A Custard miscompilation of
   the extracted checker once deleted that check, letting [caller] verify:
   see tests/custard/TacAnyArm.fst. *)
noeq type t = { a: int; b: int }

fn write (r: ref t) (x: t)
  requires exists* v. pts_to r v
  ensures pts_to r x
{ r := x }

[@@expect_failure [228]]
fn caller (r: ref t) (#y: erased t)
  requires exists* v. pts_to r v
  ensures pts_to r y
{ write r y }

fn caller_ok (r: ref t) (y: t)
  requires exists* v. pts_to r v
  ensures pts_to r y
{ write r y }
