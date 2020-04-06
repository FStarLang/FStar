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
module TestBoundedIntegers
open BoundedIntegers
let x : int32 = 1l
let y : int32 = 2l

let g (x:int32) : int32 = if x < BoundedIntegers.int32_max_value then x + 1l else x
let f (x:int32{0 <= x}) (y:int32{0 <= y /\ y <= x}) : int32 = x - ((x - y) / 2l)
let h (x:int32{0 <= x}) (y:int32{0 <= y /\ y <= x}) : int32 = (x + y) / 2l
