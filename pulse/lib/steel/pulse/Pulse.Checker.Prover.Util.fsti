module Pulse.Checker.Prover.Util

open Pulse.Syntax
open Pulse.Typing

module T = FStar.Tactics.V2
module PS = Pulse.Checker.Prover.Substs

val debug_prover (g:env) (s:unit -> T.Tac string) : T.Tac unit
