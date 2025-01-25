(*
   Copyright 2008-2024 Microsoft Research

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
module FStarC.Options.Ext

open FStarC.Effect

type key   = string
type value = string

new
val ext_state : Type0

(* Set a key-value pair in the map *)
val set (k:key) (v:value) : unit

(* Get the value from the map, or return "" if not there *)
val get (k:key) : value

(* Get a list of all KV pairs that "begin" with k, considered
as a namespace. *)
val getns (ns:string) : list (key & value)

(* List all pairs *)
val all () : list (key & value)

val save () : ext_state
val restore (s:ext_state) : unit

val reset () : unit
