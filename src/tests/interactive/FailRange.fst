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
module FailRange
open FStar.Tactics

let a : unit =
  assert_by_tactic (True /\ True)
    (fun () -> split (); fail "A")

let b () : unit =
  assert_by_tactic (True /\ True)
    (fun () -> split (); fail "B")

let c : unit =
  assert_by_tactic (True /\ True)
    (fun () -> fail "C")

let d () : unit =
  assert_by_tactic (True /\ True)
    (fun () -> fail "D")
