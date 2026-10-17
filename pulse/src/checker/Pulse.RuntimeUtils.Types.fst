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

(* The types of Pulse.RuntimeUtils.  They live apart from it because the
   checker sees only that module's interface, so Custard treats every type
   declared there as realized and expects the implementation to define it by
   name (doc/ref/custard.md, section 8.2); here they are ordinary types. *)
module Pulse.RuntimeUtils.Types

(* Ranges are unsealed: range-observing reflection functions are now unsealed in ulib. *)
let range = FStar.Range.range

type context = FStar.Sealed.Inhabited.sealed #(list (string & option range)) []
