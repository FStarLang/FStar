(*
   Copyright 2024 Microsoft Research

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

module Pulse.Extract.Main

open Pulse.Syntax.Base

module R = FStar.Reflection
module T = FStar.Tactics.V2

exception Extraction_failure of string

open Pulse.Typing.Env { env }

val extract_pulse_dv (g: env) (p:st_term) : T.Tac R.term
val extract_dv_recursive (g: env) (p:st_term) (rec_name:R.fv) : T.Tac R.term
val extract_dv_ghost (g: env) (p:st_term) : T.Tac R.term