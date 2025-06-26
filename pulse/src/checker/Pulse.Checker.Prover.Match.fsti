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

module Pulse.Checker.Prover.Match

module T = FStar.Tactics
open FStar.Pprint

open Pulse.Checker.Prover.Base

(* Full matching passes. *)

val match_syntactic (#preamble:preamble) (pst:prover_state preamble)
: T.Tac (list (list document) & pst':prover_state preamble { pst' `pst_extends` pst })

val match_fastunif (#preamble:preamble) (pst:prover_state preamble)
: T.Tac (list (list document) & pst':prover_state preamble { pst' `pst_extends` pst })

val match_fastunif_i (#preamble:preamble) (pst:prover_state preamble)
: T.Tac (list (list document) & pst':prover_state preamble { pst' `pst_extends` pst })

val match_full (#preamble:preamble) (pst:prover_state preamble)
: T.Tac (list (list document) & pst':prover_state preamble { pst' `pst_extends` pst })
