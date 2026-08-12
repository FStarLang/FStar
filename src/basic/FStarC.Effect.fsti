(*
   Copyright 2008-2017 Microsoft Research

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

module FStarC.Effect

assume effect ALL

assume sub_effect PURE ~> ALL
assume sub_effect GHOST ~> ALL
assume sub_effect DIV ~> ALL

effect All (a:Type) = ALL a

effect ML (a:Type) = ALL a

new
val ref (a:Type) : Type0

val (!) (#a:Type) (r:ref a)
  : ML a

val (:=) (#a:Type) (r:ref a) (x:a)
  : ML unit

val alloc (#a:Type) (x:a) : ML (ref a)
let mk_ref #a x = alloc #a x

val raise (e: exn) : ML 'a

val exit : int -> ML 'a

val try_with : (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a

exception Failure of string

val failwith : string -> ML 'a
