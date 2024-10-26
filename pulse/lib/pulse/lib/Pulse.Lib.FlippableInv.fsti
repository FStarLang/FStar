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

module Pulse.Lib.FlippableInv
#lang-pulse

open Pulse.Lib.Pervasives

val finv (p:slprop) : Type0

val off #p (fi : finv p) : slprop
val on  #p (fi : finv p) : slprop

val mk_finv (p:slprop) : stt (finv p) emp (fun x -> off x)

val iname_of #p (f : finv p) : iname


atomic
fn flip_on (#p:slprop) (fi : finv p)
  requires off fi ** p ** later_credit 1
  ensures on fi
  opens [iname_of fi]



atomic
fn flip_off (#p:slprop) (fi : finv p)
  requires on fi ** later_credit 1
  ensures  off fi ** p
  opens [iname_of fi]

