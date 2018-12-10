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
module Registers.IntList.Test
open Registers.IntList

let regs = regmap

(*  None of these tests can be run in a reasonable amount of time
//     with the interpreter. But they run pretty quickly with native
//     compilation *)
let concrete_integer_map  =
    let r = identity_map 10000 (create 0) in
    assert_norm (sel r 10000 == 10000)

// let symbolic_map_contents_1 (x:nat) (y:nat) =
//     let r = const_map_n 10000 x (create y) in
//     assert (normalize_term (sel r 10000) == x)

// let symbolic_map_contents_2 (x:nat) (y:nat) =
//     let r = const_map_n 10000 x (create y) in
//     assert (normalize_term (sel r 20000) == y)

// /// Not sure why, but this one fails to actually normalize
// /// Turn on this debugging flag to see the unnormalized term fed to Z3
// /// Needs to be debugged
// let symbolic_map_contents_3 (x:nat) (y:nat) =
//     let r = const_map_n 1000 x (create y) in
//     assert_norm (sel r 1000 == x);
//     assert_norm (sel r 1001 == y)
