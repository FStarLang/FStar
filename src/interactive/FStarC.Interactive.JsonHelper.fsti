(*
   Copyright 2019 Microsoft Research

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

(* Json helpers mainly for FStarC.Interactive.Lsp; some sharing with *
 * FStarC.Interactive.Ide                                            *)

module FStarC.Interactive.JsonHelper
open FStarC
open FStarC.Errors
open FStarC.Json

// Type of an associative array
type assoct = list (string & json)

val try_assoc : string -> assoct -> option json // nothrow

exception InvalidQuery of string
exception UnexpectedJsonType of string & json

val write_json : json -> unit
val js_fail : string -> json -> 'a

val js_int : json -> int
val js_bool : json -> bool
val js_str : json -> string
val js_list : (json -> 'a) -> json -> list 'a
val js_assoc : json -> assoct
val json_debug: json -> string