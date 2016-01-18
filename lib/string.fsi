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
module FStar.String

val split:   list char -> string -> Tot (list string)
val strcat:  string -> string -> Tot string
val concat:  string -> list string -> Tot string
val compare: string -> string -> Tot int
val strlen:  string -> Tot nat
val length:  string -> Tot nat
val lowercase: string -> Tot string

(* may fail with index out of bounds *)
val substring: string -> int -> int -> string
val get: string -> int -> char 
val collect: (char -> string) -> string -> string
