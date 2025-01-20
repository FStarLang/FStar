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

module FStarC.Plugins

open FStarC.Effect
include FStarC.Plugins.Base

val load_plugin          : string -> unit
val load_plugins         : list string -> unit
val load_plugins_dir     : string -> unit
val compile_modules      : string -> list string -> unit

(* Tries to load a plugin named like the extension. Returns true
if it could find a plugin with the proper name. This will fail hard
if loading the plugin fails. *)
val autoload_plugin (ext:string) : bool
