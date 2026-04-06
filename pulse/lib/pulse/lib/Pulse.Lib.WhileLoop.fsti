module Pulse.Lib.WhileLoop
#lang-pulse

open Pulse.Main
open Pulse.Lib.Core

(* Not to be called directly. *)

fn while_loop
  (inv:slprop)
  (post:bool -> slprop)
  (cond:unit -> stt bool inv (fun b -> post b))
  (body:unit -> stt unit (post true) (fun _ -> inv))
  requires inv
  ensures post false