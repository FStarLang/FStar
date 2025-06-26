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
open Pulse.Main

module T = FStar.Tactics

val shift :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp:slprop) ->
  (concl:slprop) ->
  slprop

ghost
fn intro_shift
  (#[T.exact (`emp_inames)] is:inames)
  (hyp concl:slprop)
  (extra:slprop)
  {| duplicable extra |}
  (f_elim: unit -> (
    stt_ghost unit is
    (extra ** hyp)
    (fun _ -> concl)
  ))
  requires extra
  ensures  shift #is hyp concl

ghost
fn elim_shift
  (#[T.exact (`emp_inames)] is:inames)
  (hyp concl:slprop)
  opens is
  requires shift #is hyp concl ** hyp
  ensures  concl

ghost
fn shift_sub_inv
  (#is1:inames)
  (#is2:inames { inames_subset is1 is2 })
  (hyp concl:slprop)
  requires shift #is1 hyp concl
  ensures  shift #is2 hyp concl

ghost
fn shift_dup
  (#is : inames)
  (p q : slprop)
  requires shift #is p q
  ensures  shift #is p q ** shift #is p q

ghost
fn shift_compose
  (#is : inames)
  (p q r : slprop)
  requires shift #is p q ** shift #is q r
  ensures  shift #is p r
