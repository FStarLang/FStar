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
module T = FStar.Tactics

val stick  :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop

let ( @==> ) :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop
  = fun #is -> stick #is

val elim_stick
  (#[T.exact (`emp_inames)] is: inames)
  (hyp concl: vprop)
: stt_ghost unit is
    ((stick #is hyp concl) ** hyp)
    (fun _ -> concl)

val intro_stick
  (#[T.exact (`emp_inames)] is : inames)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: unit -> (
    stt_ghost unit is
    (v ** hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit emp_inames
    v
    (fun _ -> stick #is hyp concl)

val stick_sub_inv
  (#os1 : inames)
  (#os2 : inames{inames_subset os1 os2})
  (hyp concl: vprop)
: stt_ghost unit emp_inames
    (stick #os1 hyp concl)
    (fun _ -> stick #os2 hyp concl)