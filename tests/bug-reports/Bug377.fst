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
module Bug377

open FStar.Relational.Comp
open FStar.Relational.Relational

type ni_exp (l:unit) = unit -> St2 (double int)

val expr : unit -> Tot (ni_exp ())
(* The inlined version works *)
(* val expr : unit -> Tot (unit -> St2 (double int)) *)
let expr () = fun () -> compose2 (fun _ -> 0) (fun _ -> 0) (twice ())

(* This also works *)
val expr' : unit -> Tot (ni_exp ())
let expr' () = (fun () -> compose2 (fun _ -> 0) (fun _ -> 0) (twice ()))
