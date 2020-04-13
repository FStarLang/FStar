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
module AnotType

[@(expect_failure [309])]
type tc : int = | C

type ta : Type = | A

type tb : Type u#42 = | B

(* Fails, Type0 != Type42 *)
[@(expect_failure [189])]
let _ = ta == tb

type td : eqtype = | D

type te : int -> eqtype = | Ea : te 1
                          | Eb : te 1
                          | Ec : te 8
                          | Ed : te 99


(* This has to work without SMT, since `td` was annotated as an eqtype.
 * We need not unfold and see the relevant `hasEq`. *)
#set-options "--no_smt"
let f (x y : td) = x = y

let _ = Ea = Eb
