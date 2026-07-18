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

module Pulse.Config

open FStar.Tactics.V2

val join_goals : bool

(* Checks if a boolean debug flag `s` is enabled, i.e.
if the extension option `pulse:s` was given, and its value
is not "0" or "false". *)
val debug_flag : string -> Tac bool
