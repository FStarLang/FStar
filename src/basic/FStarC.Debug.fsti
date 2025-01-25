(*
   Copyright 2008-2020 Microsoft Research

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

module FStarC.Debug

open FStar open FStarC
open FStarC
open FStarC.Effect

(* State handling for this module. Used by FStarC.Options, which
is the only module that modifies the debug state. *)
val saved_state : Type0
val snapshot () : saved_state
val restore (s:saved_state) : unit

(* Enable debugging. This will make any() return true, but
does not enable any particular toggle. *)
val enable () : unit

(* Are we doing *any* kind of debugging? *)
val any () : bool

(* Print a quick message on stdout whenever debug is on. If the string
is not a constant, put this under an if to thunk it. *)
val tag (s : string) : unit

(* Obtain the toggle for a given debug key *)
val get_toggle (k : string) : ref bool

(* List all registered toggles *)
val list_all_toggles () : list string

(* Vanilla debug levels. Each level implies the previous lower one. *)
val low     () : bool
val medium  () : bool
val high    () : bool
val extreme () : bool

(* Enable a list of debug toggles. If will also call enable()
is key is non-empty, and will recognize "Low", "Medium",
"High", "Extreme" as special and call the corresponding
set_level_* function. *)
val enable_toggles (keys : list string) : unit

(* Sets the debug level to zero and sets all registered toggles
to false. any() will return false after this. *)
val disable_all () : unit

(* Nuclear option: enable ALL debug toggles. *)
val set_debug_all () : unit

(* Not used externally at the moment. *)
val set_level_low     () : unit
val set_level_medium  () : unit
val set_level_high    () : unit
val set_level_extreme () : unit
