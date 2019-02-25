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
#light "off"
module FStar.String
open FStar.ST
open FStar.All
open Prims
open FStar.Char
open FStar.BigInt

(* The name of this file is misleading: most string functions are to be found in
   util.fsi *)
val make:    int -> char -> string
val split:   chars: list<char> -> s: string -> Tot<list<string>>
val strcat:  string -> string -> Tot<string>
val concat:  separator: string -> strings: list<string> -> Tot<string>
val compare: s1: string -> s2: string -> Tot<int>
val strlen:  string -> Tot<nat>
val length:  string -> Tot<nat>
val lowercase: string -> Tot<string>
val uppercase: string -> Tot<string>
val escaped: string -> Tot<string>

(* may fail with index out of bounds *)
val substring: string -> start:int -> len:int -> string
val get: string -> int -> char
val collect: (char -> string) -> string -> string
val index_of: string -> char -> bigint
val index: string -> bigint -> char

val list_of_string : string -> list<char>
val string_of_list: list<char> -> string
val (^) : string -> string -> string