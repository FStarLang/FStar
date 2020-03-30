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
module ExpectFailure

(* Checking that the definition fails *)
[@ expect_failure]
let _ = 1 + 'a'

(* Checking that it raises one specific error code, and no others *)
[@ (expect_failure [189])]
let _ = 1 + 'a'

(* Same semantics for verification errors *)
[@ expect_failure]
let _ = assert False
[@ (expect_failure [19])]
let _ = assert False

(* Now for interaction with --lax *)
#set-options "--lax"

(* These are ignored, since we're laxing and using the ordinary `expect_failure` *)
[@expect_failure]
let _ = assert False
[@expect_failure]
let _ = assert True

(* We can use expect_lax_failure to ask for a lax-checking failure *)
[@expect_lax_failure]
let _ = 1 + 'a'

#reset-options ""

(* Expecting a lax failure can be done without --lax too, the flag
 * will be internally set when `expect_lax_failure` is specified. *)
[@expect_lax_failure]
let _ = 1 + 'a'

(* These two would fail (to fail :) ), since they lax-check correctly *)
//[@expect_lax_failure]
//let _ = assert False
//
//[@expect_lax_failure]
//let _ = assert True

(* We can also specify the expected errors *)
[@ (expect_lax_failure [189])]
let _ = 1 + 'a'
