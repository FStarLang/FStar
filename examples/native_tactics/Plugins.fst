(*
   Copyright 2008-2018 Microsoft Research

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
module Plugins

(* Tests for generating bindings to native plugins with correct calls to the
   embedding and unembedding functions for the types supported in tactic compilaton.
   Tactics should be generated without warnings and compile without errors.
*)

open FStar.Reflection
open FStar.Tactics

[@plugin]
let int_plugin: int -> int = id

[@plugin]
let bool_plugin: bool -> bool = id

[@plugin]
let unit_plugin: unit -> bool = fun _ -> true

[@plugin]
let string_plugin: string -> string = id

[@plugin]
let term_plugin: term -> term = id

[@plugin]
let binder_plugin: binder -> binder = id

[@plugin]
let binders_plugin: binders -> binders = id

[@plugin]
let norm_step_plugin: norm_step -> norm_step = id

[@plugin]
let fv_plugin: fv -> fv = id

[@plugin]
let list_plugin: list int -> (list int) = id

[@plugin]
let option_plugin: option term -> (option term) = id

[@plugin]
let tuple_plugin: int -> bool -> (int * bool) = fun x y -> (x,y)

[@plugin]
let any_plugin (#a: Type) (l: list a): list a = l
