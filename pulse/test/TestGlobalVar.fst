module TestGlobalVar
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Class.Duplicable
module G = Pulse.Lib.GlobalVar

assume val p : int -> slprop
assume val dup_p : (x:int -> duplicable (p x))
assume val init : unit -> stt int emp (fun x -> p x)

(* [mk_gvar] is nondeterministic, so a global may still be defined at the
   top level (no warning 272, no [nonempty] obligation). *)
let g1 : G.gvar p = G.mk_gvar #_ #_ #dup_p init
let g2 : G.gvar p = G.mk_gvar #_ #_ #dup_p init

(* But two globals with the same initializer must not be identified: at
   runtime each [let] gets its own call to [init]. See issue #4534. *)
[@@expect_failure [19]]
let bad () : squash (g1 == g2) = ()

[@@expect_failure [19]]
let bad_ghost () : squash (G.read_gvar_ghost g1 == G.read_gvar_ghost g2) = ()

(* A global is of course equal to itself. *)
let good () : squash (g1 == g1) = ()

let good_ghost () : squash (G.read_gvar_ghost g1 == G.read_gvar_ghost g1) = ()
