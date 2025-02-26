module Pulse.Lib.WhileLoop
#lang-pulse

open Pulse.Main
open Pulse.Lib.Core

(* Not to be called directly. *)

fn while_loop
  (inv : bool -> slprop)
  (cond : stt bool (exists* x. inv x) (fun b -> inv b))
  (body : stt unit (inv true) (fun _ -> exists* x. inv x))
  requires exists* x. inv x
  ensures inv false
