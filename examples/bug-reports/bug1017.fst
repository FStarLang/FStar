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
module Bug1017

(* Should not be accepted, the body is still in `Tot` *)
let rec loop (x : int) : Tot (int -> Dv int) = loop (x - 1)

(* Neither should this one. It also generates invalid OCaml: *)
(* > Error: This kind of expression is not allowed as right-hand side of `let rec' *)
let rec loop2 : Tot (unit -> Dv unit) = loop2

(* This one is OK, as it will only diverge when applied *)
let rec ok (u:unit) : Dv unit = ok ()

(*
 * Causes normalizer to loop. And to use an increasing amount of heap,
 * so I suspect GC is not kicking in (separate issue?)
 *)
let _ = assert_norm (loop 1 == ((fun x -> x) <: int -> Dv int))

(* This loops in extracted OCaml *)
let y : int -> Dv int = loop 42
