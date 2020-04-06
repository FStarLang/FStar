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
module Bug379

(* Always worked *)
val test1 : nat -> nat -> Tot nat
let rec test1 x y = if x = 0 then y else test1 0 y

(* Still fails *)
val test2 : nat -> Tot (nat -> Tot nat)
let rec test2 x y = if x = 0 then y else test2 0 y

(* Now works too *)
val test3 : nat -> Tot ( nat -> Dv nat)
let rec test3 x y = if x = 0 then y else test3 0 y
