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
module ExtractionBug03

let rec type_of_nat (n:nat) = bool

module D=ExtractionBug03Dep
let test (x:int) = D.create #(type_of_nat 0) 0 true

// type t =
//  | MkT : int -> t

// exception Foo of int
// // unfold
// // let f (x:int) = x

// // let g x = f x
