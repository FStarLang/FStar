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

module Pulse.Class.Introducable
open Pulse.Lib.Core
module T = FStar.Tactics.V2
#lang-pulse

[@@erasable; FStar.Tactics.Typeclasses.fundeps [3]]
class introducable (is: inames) (extra: slprop) (concl: slprop) (t: Type u#a) = {
  intro_aux : t -> stt_ghost unit is extra (fun _ -> concl);
}

instance introducable_base is extra concl :
    introducable is extra concl (stt_ghost unit is extra (fun _ -> concl)) =
  { intro_aux = id }

let intro
    (#[T.exact (`emp_inames)] is: inames)
    (concl: slprop)
    (#[T.exact (`emp)] extra: slprop)
    #t {| introducable is extra concl t |} (k: unit -> t) :
    stt_ghost unit is extra (fun _ -> concl) =
  intro_aux #is #extra #concl (k ())
