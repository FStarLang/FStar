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
module Bug241

val test1 : (nat & unit)
let test1 = 2, ()

val test2 : (int & unit)
[@@expect_failure [19]]
let test2 = test1

val coerce : (nat & unit) -> (int & unit)
let coerce p = let (x1,x2) = p in (x1,x2)

val test2' : (x:int * unit)
let test2' = coerce test1
