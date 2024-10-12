(*
   Copyright 2008-2023 Microsoft Research

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

module FStarC.Char

(* This is a trimmed-down version of ulib/FStar.Char, realized by the
same ML implementation. It is here to prevent dependencies from the
compiler into the UInt32 module. *)

new
val char:eqtype

type char_code

val int_of_char : char -> Tot int
val char_of_int : int -> Tot char

val lowercase: char -> Tot char
val uppercase: char -> Tot char