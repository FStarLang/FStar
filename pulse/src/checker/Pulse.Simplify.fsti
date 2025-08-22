module Pulse.Simplify

(* Some functions to simplify terms and slprops *)

open FStar.Reflection.V2
module T       = FStar.Tactics.V2

val simplify (t:term) : T.Tac term