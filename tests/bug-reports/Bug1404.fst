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
module Bug1404

(* This should fail with :
 * bug1404.fst(9,6-10,17): (Error 297) Patterns in this match are incoherent, variable y is bound in some but not all patterns.
 *)
let f o =
    match o with
    | (Some x, _)
    | (x, Some y) -> y
    | _ -> false
