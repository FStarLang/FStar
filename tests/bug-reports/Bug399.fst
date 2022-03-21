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
module Bug399

open FStar.ST

type foo = unit -> St unit

val fail1 : (unit * foo) -> unit
let fail1 p = assert (fst p = fst p)

val fail2 : (unit * foo) -> unit
let fail2 p = let x = fst p in
              let y = fst p in
              assert (y = x)

val works : (unit * foo) -> unit
let works p = let x = match p with
                      | a,b -> a in
              let y = match p with
                      | a,b -> a in
              assert (y = x)
