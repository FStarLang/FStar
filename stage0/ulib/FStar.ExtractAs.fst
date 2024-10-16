(*
   Copyright 2024 Microsoft Research

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

module FStar.ExtractAs
open FStar.Stubs.Reflection.Types

(** Replaces the annotated definition
    by the specified implementation during extraction.
    There are no checks whether the implementation
    has the same semantics, or even the same type.

    For example, if you have:

    [@@extract_as (`(fun (x: nat) -> "not a number"))]
    let add_one (x: nat) : nat = x + 42

    Then `add_one` will extract to `let add_one x = "not a number"`,
    and most likely cause the extracted program to crash.

    Note that the argument needs to be a literal quotation.
    The implementation can be recursive,
    but then you need to construct the attribute via a tactic.
 *)
let extract_as (impl: term) = ()
