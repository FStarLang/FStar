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

type char = FStar.Char.char

val list_of_string : string -> Tot (list char)
val string_of_list : list char -> Tot string

(* Not much in here; we should extend and refine this interface *)

noextract
let strlen s = List.length (list_of_string s)
unfold let length s = strlen s

(**
 When applied to a literal s of less than n characters, this predicate
 reduces to True before going to the SMT solver.
 Otherwise, the left disjunct reduces partially but the right disjunct
 remains as is, allowing to keep `strlen s <= n` in the context.
*)
unfold let maxlen s n = b2t (normalize_term (strlen s <= n)) \/ strlen s <= n

val make: l:nat -> char -> Tot (s:string {length s = l})
val split:   list char -> string -> Tot (list string)
val strcat:  s0:string -> s1:string -> Tot (s:string{length s = length s0 + length s1})
unfold let (^) s0 s1 = strcat s0 s1
val concat:  string -> list string -> Tot string
val compare: string -> string -> Tot int

val lowercase:  string -> Tot string
val uppercase:  string -> Tot string

val index: s:string -> n:nat {n < length s} -> Tot char
//index_of: returns -1 if the char is not found, for compatibility with C
val index_of: string -> char -> Tot int
val sub: s:string -> i:nat -> l:nat{i + l <= length s} -> Tot char

(* may fail with index out of bounds *)
(* Second argument is a length, not an index. *)
val substring: string -> int -> int -> string
val get: string -> int -> char
val collect: (char -> string) -> string -> string

let string_of_char (c:char) : Tot string = make 1 c
