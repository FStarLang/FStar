(*
   Copyright 2019 and Microsoft Research

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

(* Json helpers mainly for FStarC.Interactive.Ide                                            *)

module FStarC.Interactive.JsonHelper
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Errors
open FStarC.Range
open FStarC.Json
open FStarC.TypeChecker.Env
open FStarC.Class.Show

module U = FStarC.Util

let try_assoc (key: string) (d: assoct) =
  Option.map snd (U.try_find (fun (k, _) -> k = key) d)

// All exceptions are guaranteed to be caught in the LSP server implementation
exception InvalidQuery of string // Only in IDE
exception UnexpectedJsonType of string & json

let write_json (js: json) =
  Format.print_raw (string_of_json js);
  Format.print_raw "\n"

// Only used in IDE
let js_fail expected got =
  raise (UnexpectedJsonType (expected, got))

let js_int : json -> int = function
  | JsonInt i -> i
  | other -> js_fail "int" other
let js_bool : json -> bool = function
  | JsonBool b -> b
  | other -> js_fail "int" other
let js_str : json -> string = function
  | JsonStr s -> s
  | other -> js_fail "string" other
let js_list k = function
  | JsonList l -> List.map k l
  | other -> js_fail "list" other
let js_assoc : json -> assoct = function
  | JsonAssoc a -> a
  | other -> js_fail "dictionary" other


let json_debug = function
  | JsonNull -> "null"
  | JsonBool b -> Format.fmt1 "bool (%s)" (if b then "true" else "false")
  | JsonInt i -> Format.fmt1 "int (%s)" (show i)
  | JsonStr s -> Format.fmt1 "string (%s)" s
  | JsonList _ -> "list (...)"
  | JsonAssoc _ -> "dictionary (...)"