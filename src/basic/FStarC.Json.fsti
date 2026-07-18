(*
   Copyright 2008-2023 Nikhil Swamy and Microsoft Research

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
module FStarC.Json

open FStarC.Effect

type json =
| JsonNull
| JsonBool of bool
| JsonInt of int
| JsonStr of string
| JsonList of list json
| JsonAssoc of list (string & json)

val json_of_string : string -> option json
val string_of_json : json -> string
