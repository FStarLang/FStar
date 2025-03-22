(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Checker.Prover.Match.MKeys

open FStar.Tactics.V2
open Pulse.Syntax
open Pulse.Typing

(* remove!*)
val same_head (t0 t1 : term): Tac bool

val eligible_for_smt_equality (g:env) (t0 t1 : term) : Tac bool

val mkey_mismatch (g:env) (t0 t1 : term) : Tac bool
