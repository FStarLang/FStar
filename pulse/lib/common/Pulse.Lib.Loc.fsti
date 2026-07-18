(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.Loc
open FStar.Ghost

[@@erasable] val loc_id : Type0

val process_of : loc_id -> loc_id
val process_of_idem (l:loc_id) : Lemma (process_of (process_of l) == process_of l)
  [SMTPat (process_of (process_of l))]

val dummy_loc : loc_id

inline_for_extraction noextract instance non_informative_loc_id
  : NonInformative.non_informative loc_id
  = { reveal = (fun x -> reveal x) <: NonInformative.revealer loc_id }
