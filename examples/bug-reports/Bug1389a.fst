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
module Bug1389a

assume val or_else : (#a:Type) -> (f : (unit -> Ex a)) -> (g : (unit -> Ex a)) -> Ex a
assume val fail : (#a:Type) -> string -> Ex a

let rec first #a (ts : list (unit -> Ex a)) : Ex a =
    match ts with
    | [] -> fail "no tactics to try"
    | t::ts -> or_else #a t (first #(unit -> Ex a) ts)

let first2 #a (ts : list (unit -> Ex a)) : Ex a =
    match ts with
    | [] -> fail "no tactics to try"
    | t::ts -> or_else #a t (first #(unit -> Ex a) ts)

// fails appropriately
(*
let rec first_int (ts : list (unit -> Ex int)) : Ex int =
    match ts with
    | [] -> fail "no tactics to try"
    | t::ts -> or_else #int t (first_int ts)
*)
