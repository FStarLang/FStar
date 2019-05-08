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
module Bug1443a

[@(expect_failure [66])]
let rec test ps = match ps with
  | [] -> 0
  | a::q ->
    let rec blah i = match i with
      | [] -> 0
      | b::r -> blah r
    in
    if a = 0 then 0
    else test q
