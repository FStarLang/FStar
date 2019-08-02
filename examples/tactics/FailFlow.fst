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
module FailFlow

open FStar.Tactics

let fail_flow () : Tac unit =
    fail "failing";
    assert False

(* This fails to typecheck, since the assert is definitely reachable *)
[@expect_failure]
let print_test () : Tac unit =
    print "not failing";
    assert False

(* None of these succeed (as in: return Success within the monad) *)
[@expect_failure]
let s_fail_flow () : TacS unit =
    fail "failing";
    assert False

[@expect_failure]
let s_print_test () : TacS unit =
    print "not failing";
    assert False
