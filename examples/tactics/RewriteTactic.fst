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
module RewriteTactic

open FStar.Tactics

assume val foo : int -> int
assume val lem1 : unit -> Lemma (foo 1 == foo 2)
assume val lem2 : (x:int) -> Lemma (foo 1 == foo x)

let tau1 () = apply_lemma (`lem1)
let tau2 () = apply_lemma (`lem2)

let test1 _ =
  assert (rewrite_with_tactic tau1 (foo 1) == (foo 2))

// SMT Failure, expected, since the SMT can't see that foo 1 == foo 2
// (without triggering lem1)
[@@expect_failure]
let test2 _ =
  assert (rewrite_with_tactic tau1 (foo 1) == (foo 1))

// Uninstantiated uvar remaining, OK, since there is no one solution for
// x in the call to lem2. Doing [exact (`n)] for any n will make it work.
[@@expect_failure]
let test3 _ =
  assert (rewrite_with_tactic tau2 (foo 1) == (foo 2))
