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

module Pulse.Checker.Prover.IntroWithPure

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Checker.Prover.Base

val intro_with_pure (#preamble:_) (pst:prover_state preamble)
  p n v
  (unsolved':list slprop)
  (_:squash (pst.unsolved == tm_with_pure p n v::unsolved'))
  (prover:prover_t)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        is_terminal pst' })
