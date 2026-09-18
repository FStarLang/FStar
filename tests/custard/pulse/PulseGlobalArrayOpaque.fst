module PulseGlobalArrayOpaque
#lang-pulse
open Pulse
module G  = Pulse.Lib.GlobalArray
module US = FStar.SizeT
module U8 = FStar.UInt8

(* Section 71.4.  A run whose contents are not known until the program runs
   is not a static array, whatever its type says.  Custard refuses it rather
   than quietly building the table in a startup pass -- which would compile,
   run, and cost exactly what the type was chosen to avoid. *)

assume val opaque_list : list U8.t

let tbl : G.static_array U8.t = G.mk_static_array opaque_list

fn main () returns r:US.t { 0sz }
