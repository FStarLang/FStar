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
module Bug613

assume val f : int -> int -> Tot int
assume val g : int -> int -> Tot int

val l : unit -> Lemma (requires (f == g))
                      (ensures (f 0 1 == g 0 1))
let l () = () (* this works *)

val l' : unit -> Lemma (requires (f 0 == g 0))
                       (ensures (f 0 1 == g 0 1))
let l' () = () (* this fails *)

(* closer to mac.fst *)
assume val h : int -> Tot int
val l'' : unit -> Lemma (requires (f 0 == h))
                       (ensures (f 0 1 == h 1))
let l'' () = () (* this fails too *)

assume val i0: int -> Tot int
assume val i1: int -> Tot int
let test_i () : Lemma (requires i0==i1) (ensures i0 0 == i1 0) = ()
