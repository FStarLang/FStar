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
module Tests

open Eq
open Add
open Num

let rec sum (#a:Type) [|additive a|] (l : list a) : a =
    match l with
    | [] -> zero
    | x::xs -> plus x (sum xs)

let sum2 (#a:Type) [|additive a|] (l : list a) : a =
    List.Tot.fold_right plus l zero

let _ = assert_norm (sum2 [1;2;3;4] == 10)
let _ = assert_norm (sum2 [false; true] == true)

let sandwich (#a:Type) [|num a|] (x y z : a) : a =
    if eq x y
    then plus x z
    else minus y z

let test1 = assert (sum [1;2;3;4;5;6] == 21)
let test2 = assert (plus 40 (minus 10 8) == 42)
