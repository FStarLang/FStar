(*
   Copyright 2008-2018 Microsoft Research

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
#light "off"
module FStar.Tactics.Result

// This file *is* extracted (unlike its twin in ulib).

// This refers to FStar.Tactics.Types.fsi in the current folder, which has the
// full definition of all relevant types (from ulib, we use an different
// interface that hides those definitions).
open FStar.Tactics.Types

type __result<'a> =
    | Success of 'a * proofstate
    | Failed  of exn       //error
              * proofstate //the proofstate at time of failure
