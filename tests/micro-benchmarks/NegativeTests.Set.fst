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
(* ******************************************************************************** *)
module NegativeTests.Set
assume type elt
assume val a : elt
assume val b : elt
assume val c : elt
assume AB_distinct: a=!=b
open FStar.TSet

val should_fail1: unit -> Tot unit
[@ (expect_failure [19])]
let should_fail1 u =
  assert (mem b (singleton a))

val should_fail2: unit -> Tot unit
[@ (expect_failure [19])]
let should_fail2 u =
  assert (subset (union (singleton a) (singleton b)) (singleton a))

val should_fail3: unit -> Tot unit
[@ (expect_failure [19])]
let should_fail3 u =
  assert (mem c (union (singleton a) (singleton b)))
