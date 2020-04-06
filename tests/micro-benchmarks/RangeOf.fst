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
module RangeOf

(* This is very basic, but we cannot really test that we assign
 * proper ranges because we keep them completely opaque to 
 * guarantee soundness. *)

let x : int = 42
let y : int = 43

let r1 : range = range_of x
let r2 : range = range_of y

(* Both of these should fail, ranges are opaque *)
(* let _ = assert (r1 == r2) *)
(* let _ = assert (r1 =!= r2) *)

let z = set_range_of y (range_of x)

let r3 = set_range_of r1 r2

(* Setting ranges has no observable behaviour *)
let _ = assert (z == y)
let _ = assert (z =!= x)
let _ = assert (r1 == r3) // Succeeds, even if opaque they are definitionally equal.

(* These two fail since they are only typeable if fully applied *)
(* let r = range_of *)
(* let s = set_range_of *)
