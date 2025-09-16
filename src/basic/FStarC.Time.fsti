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
module FStarC.Time

(* Utilities for times and dates. See FStarC.Timing for
   measuring time instead. *)

open FStarC.Effect
open FStarC.Class.Show

type time_of_day

val get_time_of_day ()
  : time_of_day

val get_time_of_day_ms ()
  : int

val is_before (t1 t2 : time_of_day)
  : bool

val get_file_last_modification_time (fn : string)
  : time_of_day

val string_of_time_of_day (t : time_of_day)
  : string

(* This is not there in the .ml file, make sure to unfold it. *)
inline_for_extraction noextract
instance showable_time_of_day : showable time_of_day = {
  show = string_of_time_of_day;
}
