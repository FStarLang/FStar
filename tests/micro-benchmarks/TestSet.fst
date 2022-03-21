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
(* Expect 5 intentional failures *)
module TestSet
assume type elt
assume val a : elt
assume val b : elt
assume val c : elt
assume AB_distinct: a=!=b
open FStar.TSet

val should_succeed: unit -> Tot unit
let should_succeed u =
  assert (mem b (union (singleton a) (singleton b)));
  assert (mem a (union (singleton a) (singleton b)));
  assert (subset (singleton a) (union (singleton a) (singleton b)));
  assert (subset (singleton b) (union (singleton a) (singleton b)));
  assert (equal (union (singleton a) (singleton b))
                (union (singleton b) (singleton a)))

