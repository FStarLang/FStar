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
module Bug807d

let t x = #y:int -> unit -> Lemma (x + y == y + x)
assume val f : x:int -> #y:int -> unit -> Lemma (x + y == y + x)

(* Works *)
val h : unit -> #y:int -> unit -> Lemma (5 + y == y + 5)
let h () = f 5

(* Used to fail *)
val g : unit -> t 5
let g () = f 5

let k (f : t 5) : #y:int -> unit -> Lemma (5 + y == y + 5) = f

let j (f : (#y:int -> unit -> Lemma (5 + y == y + 5))) : t 5 = f
