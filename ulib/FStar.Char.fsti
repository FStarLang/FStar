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

module U32 = FStar.UInt32
new val char : eqtype

val lowercase: char -> Tot char
val uppercase: char -> Tot char

type char_code = n:U32.t{U32.v n < pow2 21}
val u32_of_char: char -> Tot char_code
val char_of_u32: char_code -> Tot char
val char_of_u32_of_char:
    c:char
  -> Lemma
    (ensures (char_of_u32 (u32_of_char c) == c))
    [SMTPat (u32_of_char c)]

val u32_of_char_of_u32:
    c:char_code
  -> Lemma
    (ensures (u32_of_char (char_of_u32 c) == c))
    [SMTPat (char_of_u32 c)]

let int_of_char (c:char) : nat = U32.v (u32_of_char c)
let char_of_int (i:nat{i < pow2 21}) : char = char_of_u32 (U32.uint_to_t i)

#set-options "--lax"
//This private primitive is used internally by the
//compiler to translate character literals
//with a desugaring-time check of the size of the number,
//rather than an expensive verifiation check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __char_of_int (x:int) : char
    = char_of_int x
#reset-options
