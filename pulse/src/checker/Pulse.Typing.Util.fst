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

module T = FStar.Tactics.V2
module RU = Pulse.RuntimeUtils
(* Call check_equiv under a ForceSMT guard policy *)
let check_equiv_now tcenv t0 t1 =
  T.with_policy ForceSMT (fun () ->
    T.check_equiv tcenv t0 t1)

(* Call check_equiv without allowing
it to generate guards nor unfold. It's a very
simple use of the core checker + unifier.
The Force guard_policy is probably unneeded, as no
guards should appear. *)
let check_equiv_now_nosmt tcenv t0 t1 =
  // T.with_policy ForceSMT (fun () ->
    T.check_equiv_nosmt tcenv t0 t1

let universe_of_now g e =
  T.with_policy ForceSMT (fun () ->
    T.universe_of g e)
