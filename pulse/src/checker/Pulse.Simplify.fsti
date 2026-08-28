module Pulse.Simplify

(* Some functions to simplify terms and slprops *)

open FStar.Reflection.V2
module T       = FStar.Tactics.V2

(* Whether the `--ext pulse:extra_simplify` flag is set. *)
val extra_simplify_enabled : unit -> T.Tac bool

val simplify (t:term) : T.Tac term