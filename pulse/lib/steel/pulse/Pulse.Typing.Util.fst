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

module Pulse.Typing.Util

module L = FStar.List.Tot
module T = FStar.Tactics.V2

(* Call check_equiv under a SMTSync guard policy *)
let check_equiv_now tcenv t0 t1 =
  T.with_policy SMTSync (fun () ->
    T.check_equiv tcenv t0 t1)

let universe_of_now g e =
  T.with_policy SMTSync (fun () ->
    T.universe_of g e)
