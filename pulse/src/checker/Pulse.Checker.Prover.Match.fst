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

open Pulse.Checker.Prover.Match.Comb
open Pulse.Checker.Prover.Match.Matchers

let match_syntactic   = match_with "SYNTACTIC"      match_syntactic_11
let match_fastunif    = match_with "FASTUNIF"       match_fastunif_11
let match_fastunif_i  = match_with "FASTUNIF_INST"  match_fastunif_inst_11
let match_full        = match_with "FULL"           match_full_11
