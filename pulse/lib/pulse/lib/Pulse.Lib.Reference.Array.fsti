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

module Pulse.Lib.Reference.Array
#lang-pulse
open FStar.Ghost
open Pulse.Lib.Array.Basic
open Pulse.Class.PtsTo
open Pulse.Lib.Core
open Pulse.Lib.Reference

inline_for_extraction
unobservable
fn to_array u#a (#a: Type u#a) (r: ref a) #p (#v: erased a)
  requires r |-> Frac p v
  returns arr: array a
  ensures rewrites_to arr (to_array_ghost r)
  ensures arr |-> Frac p (seq![reveal v])
  ensures pure (length arr == 1)

inline_for_extraction
ghost
fn return_to_array u#a (#a: Type u#a) (r: ref a) #p (#v: Seq.seq a)
  requires to_array_ghost r |-> Frac p v
  requires pure (length (to_array_ghost r) == 1)
  returns _: squash (Seq.length v == 1)
  ensures r |-> Frac p (Seq.index v 0)