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

let lem1 () : Lemma (1 == 2) = admit ()
let lem2 (x:int) : Lemma (1 == x)
            = admit()

let tau1 () = apply_lemma (`lem1)
let tau2 () = apply_lemma (`lem2)

let test1 _ =
  assert (rewrite_with_tactic tau1 1 == 2)

// SMT Failure
[@expect_failure]
let test2 _ =
  assert (rewrite_with_tactic tau1 1 == 1)

// Uninstantiated uvar remaining
[@expect_failure]
let test3 _ =
  assert (rewrite_with_tactic tau2 1 == 2)
