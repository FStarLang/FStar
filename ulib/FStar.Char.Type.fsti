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

module FStar.Char.Type

(** [char] represents a Unicode codepoint. *)
new
val char : eqtype

let valid_codepoint (i:nat) : prop = i < 0xd7ff \/ (i >= 0xe000 /\ i <= 0x10ffff)

(* Chars are in a bijection with codepoints. See FStar.Char module for
machine integer versions of these two functions. *)
val char_of_int (i: nat{valid_codepoint i}) : Tot char
val int_of_char (c: char) : Tot (i:nat{valid_codepoint i})

val char_of_int_of_char (c:char)
  : Lemma (char_of_int (int_of_char c) == c)
          [SMTPat (int_of_char c)]

val int_of_char_of_int (i:nat{valid_codepoint i})
  : Lemma (int_of_char (char_of_int i) == i)
          [SMTPat (char_of_int i)]
