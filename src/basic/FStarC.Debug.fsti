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

open FStarC
open FStarC.Effect

val saved_state : Type0
val snapshot () : ML saved_state

val get_toggle (k : string) : ML (ref bool)

val restore (s:saved_state) : ML unit

val list_all_toggles () : ML (list string)

val any () : ML bool

val tag (s : string) : ML unit

val enable () : ML unit

val low     () : ML bool
val medium  () : ML bool
val high    () : ML bool
val extreme () : ML bool

val set_level_low     () : ML unit
val set_level_medium  () : ML unit
val set_level_high    () : ML unit
val set_level_extreme () : ML unit

val enable_toggles (keys : list string) : ML unit

val disable_all () : ML unit

val set_debug_all () : ML unit
