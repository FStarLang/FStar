(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

(*
   This module provides an erased type
   to abstract computationally irrelevant values.

   It relies on the GHOST effect defined in Prims.

   [erased a] is decorated with the erasable attribute
   As such,

   1. The type is considered non-informative.
      So, [Ghost (erased a)] can be subsumed to [Pure (erased a)]

   2. The compiler extracts [erased a] to [unit]

   The type is [erased a] is in a bijection with [a],
   as witnessed by the [hide] and [reveal] function.

   Importantly, computationally relevant code cannot use [reveal]
     (it's marked GTot)

   Just like Coq's prop, it is okay to use erased types
   freely as long as we produce an erased type.

*)
module FStar.Ghost

[@erasable]
noeq
type erased (a:Type) =
  | E of a

let reveal #a (E x) = x
let hide #a x = E x
let hide_reveal #a x = ()
let reveal_hide #a x = ()
