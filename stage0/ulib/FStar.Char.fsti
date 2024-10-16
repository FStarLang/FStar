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

module U32 = FStar.UInt32

(** [char] is a new primitive type with decidable equality *)
new
val char:eqtype

(** A [char_code] is the representation of a UTF-8 char code in
    an unsigned 32-bit integer whose value is at most 0x110000,
    and not between 0xd800 and 0xe000 *)
type char_code = n: U32.t{U32.v n < 0xd7ff \/ (U32.v n >= 0xe000 /\ U32.v n <= 0x10ffff)}

(** A primitive to extract the [char_code] of a [char] *)
val u32_of_char: char -> Tot char_code

(** A primitive to promote a [char_code] to a [char] *)
val char_of_u32: char_code -> Tot char

(** Encoding and decoding from [char] to [char_code] is the identity *)
val char_of_u32_of_char (c: char)
    : Lemma (ensures (char_of_u32 (u32_of_char c) == c)) [SMTPat (u32_of_char c)]

(** Encoding and decoding from [char] to [char_code] is the identity *)
val u32_of_char_of_u32 (c: char_code)
    : Lemma (ensures (u32_of_char (char_of_u32 c) == c)) [SMTPat (char_of_u32 c)]

(** A couple of utilities to use mathematical integers rather than [U32.t]
    to represent a [char_code] *)
let int_of_char (c: char) : nat = U32.v (u32_of_char c)
let char_of_int (i: nat{i < 0xd7ff \/ (i >= 0xe000 /\ i <= 0x10ffff)}) : char = char_of_u32 (U32.uint_to_t i)

(** Case conversion *)
val lowercase: char -> Tot char
val uppercase: char -> Tot char

#set-options "--admit_smt_queries true"

(** This private primitive is used internally by the compiler to
    translate character literals with a desugaring-time check of the
    size of the number, rather than an expensive verification check.
    Since it is marked private, client programs cannot call it
    directly Since it is marked unfold, it eagerly reduces,
    eliminating the verification overhead of the wrapper *)

private unfold
let __char_of_int (x: int) : char = char_of_int x
#reset-options

