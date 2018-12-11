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
module InlineLet
open FStar.HyperStack
open FStar.HyperStack.ST

noeq 
type pkg (a:Type) = 
  | Pkg : something: (a -> St (a * int))
        -> pkg a

inline_for_extraction
let pkg_something = function
    | Pkg s -> s

noeq 
type local_pkg (a:Type) = 
  | LocalPkg : local_something: (a -> St int)
        -> local_pkg a

inline_for_extraction
let local_something = function
  | LocalPkg s -> s

inline_for_extraction
let pkg_of_local_pkg #a (r:ref a) (lp:local_pkg a) =
  [@inline_let]
  let wrapper (x:a) =
      let v = !r in
      r := x;
      let b = local_something lp x in
      v, b
  in
  Pkg wrapper

assume val some_stateful_operation: int -> St int

inline_for_extraction
let ideal = false

inline_for_extraction
let maybe_ideal_op (i:int) =
    if ideal
    then some_stateful_operation i
    else i + 1

let test (r:rid) (x:bool) =
  let r : ref int = FStar.HyperStack.ST.ralloc r 0 in
  [@inline_let]
  let pkg = pkg_of_local_pkg r (LocalPkg maybe_ideal_op) in
  pkg_something pkg 16
