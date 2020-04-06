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
module ShortCircuit

let test1 = assert((true || true) = true)
let test2 = assert((true || false) = true)
let test3 = assert((false || true) = true)
let test4 = assert((false || false) = false)

let test1' = assert((true && true) = true)
let test2' = assert((true && false) = false)
let test3' = assert((false && true) = false)
let test4' = assert((false && false) = false)
