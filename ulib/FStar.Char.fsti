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

module FStar.Char

/// This module provides the [char] type, an abstract type
/// representing UTF-8 characters.
///
/// UTF-8 characters are representing in a variable-length encoding of
/// between 1 and 4 bytes, with a maximum of 21 bits used to represent
/// a code.
///
/// See https://en.wikipedia.org/wiki/UTF-8 and
/// https://erratique.ch/software/uucp/doc/unicode.html

(* The type definition is here. The rest of this module is properties.
Clients who only need the name of the type can import this smaller
Char.Type module. *)
include FStar.Char.Type

module U32 = FStar.UInt32

(** A [char_code] is the representation of a UTF-8 char code in
    an unsigned 32-bit integer whose value is at most 0x110000,
    and not between 0xd800 and 0xe000 *)
type char_code = n: U32.t{valid_codepoint (U32.v n)}

(** A primitive to extract the [char_code] of a [char] *)
val u32_of_char: c:char -> Tot (n:char_code{U32.v n == int_of_char c})

(** A primitive to promote a [char_code] to a [char] *)
val char_of_u32: n:char_code -> Tot (c:char{c == char_of_int (U32.v n)})

(* These two are provable from the lemmas in FStar.Char.Type. *)
val char_of_u32_of_char (c: char)
    : Lemma (ensures (char_of_u32 (u32_of_char c) == c)) [SMTPat (u32_of_char c)]
val u32_of_char_of_u32 (c: char_code)
    : Lemma (ensures (u32_of_char (char_of_u32 c) == c)) [SMTPat (char_of_u32 c)]

(** Case conversion *)
val lowercase: char -> Tot char
val uppercase: char -> Tot char

#push-options "--admit_smt_queries true"
(** This private primitive is used internally by the compiler to
    translate character literals with a desugaring-time check of the
    size of the number, rather than an expensive verification check.
    Since it is marked private, client programs cannot call it
    directly Since it is marked unfold, it eagerly reduces,
    eliminating the verification overhead of the wrapper *)

private unfold
let __char_of_int (x: int) : char = char_of_int x
#pop-options
