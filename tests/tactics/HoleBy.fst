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
module HoleBy

open FStar.Tactics

let x : int = _ by (exact (`1))
let _ = assert (x == 1)

[@(expect_failure [228])]
let _ : int = _ by (exact (`1); fail "")

[@(expect_failure [228])]
let lem1 x = () <: squash (x + 1 == 1 + x)
                by fail ""

val lem2 : (x:int) -> (y:int) -> Lemma (x + y == y + x)
let lem2 x y =
    () <: _ by smt ()

val lem3 : (x:int) -> (y:int) -> Lemma (x + y == y + x)
[@(expect_failure [228])]
let lem3 x y =
    () <: _ by fail ""
