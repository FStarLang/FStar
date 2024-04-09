(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.Stick

open Pulse.Lib.Core

val stick  :
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop

let ( @==> ) :
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop
  = stick

val elim_stick
  (hyp concl: vprop)
: stt_ghost unit emp_inames
    ((stick hyp concl) ** hyp)
    (fun _ -> concl)

val intro_stick
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: unit -> (
    stt_ghost unit emp_inames
    (v ** hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit emp_inames
    v
    (fun _ -> stick hyp concl)
