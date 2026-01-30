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

module Bug113
#lang-pulse

open Pulse.Lib.Core

assume
val p : nat -> slprop
assume
val f : (x:bool -> #index:nat -> stt bool (p index) (fun _ -> emp))

[@@ expect_failure]

fn apply_with_imps_inst3 (x:bool) (#i:erased nat)
    requires p i
    returns b:bool
{
    f x
}

