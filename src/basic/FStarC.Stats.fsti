(*
   Copyright 2008-2025 Nikhil Swamy and Microsoft Research

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
module FStarC.Stats

open FStarC.Effect

(* We only record stats when this is set to true. This is
set by the Options module. *)
val enabled : ref bool

(* This is set to true by the Options module whenever
--stats true is passed, and never set to false. We use it
to decide whether to print the stats at the end of
the run. *)
val ever_enabled : ref bool

(* Count the time taken by `f ()` under a given stats key. *)
val record
  (key : string)
  (f : unit -> 'a)
  : 'a

(* Generates a message with a table for all stat keys. *)
val print_all () : string
