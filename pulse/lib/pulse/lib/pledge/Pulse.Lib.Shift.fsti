(*
   Copyright 2024 Microsoft Research

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

module Pulse.Lib.Shift
#lang-pulse
open Pulse.Class.Duplicable
open Pulse.Lib.Core

module T = FStar.Tactics

val shift :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp:slprop) ->
  (concl:slprop) ->
  slprop

val intro_shift
  (#[T.exact (`emp_inames)] is:inames)
  (hyp concl:slprop)
  (extra:slprop)
  {| duplicable extra |}
  (f_elim: unit -> (
    stt_ghost unit is
    (extra ** hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit emp_inames
    extra
    (fun _ -> shift #is hyp concl)

val elim_shift
  (#[T.exact (`emp_inames)] is:inames)
  (hyp concl:slprop)
: stt_ghost unit is
    (shift #is hyp concl ** hyp)
    (fun _ -> concl)

val shift_sub_inv
  (#is1:inames)
  (#is2:inames { inames_subset is1 is2 })
  (hyp concl:slprop)
: stt_ghost unit emp_inames
    (shift #is1 hyp concl)
    (fun _ -> shift #is2 hyp concl)

val shift_dup
  (#is : inames)
  (p q : slprop)
: stt_ghost unit
    emp_inames
    (shift #is p q)
    (fun _ -> shift #is p q ** shift #is p q)

val shift_compose
  (#is : inames)
  (p q r : slprop)
: stt_ghost unit
    emp_inames
    (shift #is p q ** shift #is q r)
    (fun _ -> shift #is p r)

