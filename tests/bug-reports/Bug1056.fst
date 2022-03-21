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
module Bug1056

open FStar.All
open FStar.ST

(* Bound variables 'c#246404' escapes; add a type annotation
let new_counter_no_annot init =
  let c = alloc init in
  fun () -> c := !c + 1; !c
*)

(* This works *)
val new_counter_ml : int -> ML (unit -> ML int)
let new_counter_ml init =
  let c = alloc init in
  fun () -> c := !c + 1; !c

(* This does not work, but it should! *)
val new_counter : int -> St (unit -> St int)
let new_counter init =
  let c = alloc init in
  fun () -> c := !c + 1; !c
(* (Error) assertion failed(Also see: /home/hritcu/Projects/fstar/pub/ulib/FStar.ST.fst(31,26-31,40)) *)
