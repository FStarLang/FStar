module PulseGlobalArrayEmpty
#lang-pulse
open Pulse
module G  = Pulse.Lib.GlobalArray
module US = FStar.SizeT
module U8 = FStar.UInt8

(* Section 71.4.  [t x[0]] is a constraint violation in C, and a run with no
   elements has no address to hand out either -- so this is a refusal and not
   something to work around with a one-element dummy. *)

let tbl : G.static_array U8.t = G.mk_static_array []

fn main () returns r:US.t { 0sz }
