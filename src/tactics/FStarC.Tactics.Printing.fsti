(*
   Copyright 2008-2016 Microsoft Research

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

module FStarC.Tactics.Printing

open FStarC.Tactics.Types

(* Dump a proofstate into the CLI or Emacs *)
val do_dump_proofstate     : proofstate -> string -> unit

(* Only for deubgging *)
val goal_to_string         : string -> option (int & int) -> proofstate -> goal -> string
val goal_to_string_verbose : goal -> string
