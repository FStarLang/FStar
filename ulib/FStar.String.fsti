(*
   Copyright 2008-2019 Microsoft Research

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
open FStar.List.Tot
(* String is a primitive type in F*.

   Most of the functions in this interface have a special status in
   that they are:

   1. All the total functions in this module are handled by F*'s
      normalizers and can be reduced during typechecking

   2. All the total functions, plus two functions in the ML effect,
      have native OCaml implementations in FStar_String.ml

   These functions are, however, not suitable for use in Low* code,
   since many of them incur implicit allocations that must be garbage
   collected.

   For strings in Low*, see LowStar.String, LowStar.Literal etc.
*)

type char = FStar.Char.char

/// `list_of_string` and `string_of_list`: A pair of coercions to
/// expose and pack a string as a list of characters
val list_of_string : string -> Tot (list char)
val string_of_list : list char -> Tot string

/// A pair
val string_of_list_of_string (s:string)
  : Lemma (string_of_list (list_of_string s) == s)
val list_of_string_of_list (l:list char)
  : Lemma (list_of_string (string_of_list l) == l)

/// `strlen s` counts the number of utf8 values in a string
/// It is not the byte length of a string
let strlen s = List.length (list_of_string s)

/// `length`, an alias for `strlen`
unfold
let length s = strlen s

/// `maxlen`: When applied to a literal s of less than n characters,
/// `maxlen s n` reduces to `True` before going to the SMT solver.
/// Otherwise, the left disjunct reduces partially but the right
/// disjunct remains as is, allowing to keep `strlen s <= n` in the
/// context.
unfold
let maxlen s n = b2t (normalize_term (strlen s <= n)) \/ strlen s <= n

/// `make l c`: builds a string of length `l` with each character set
/// to `c`
val make: l:nat -> char -> Tot (s:string {length s = l})

/// `string_of_char`: A convenient abbreviation for `make 1 c`
let string_of_char (c:char) : Tot string = make 1 c

/// `split cs s`: splits the string by delimiters in `cs`
val split:   list char -> string -> Tot (list string)

/// `concat s l` concatentates the strings in `l` delimited by `s`
val concat:  string -> list string -> Tot string

/// `compare s0 s1`: lexicographic ordering on strings
val compare: string -> string -> Tot int

/// `lowercase`: transform each character to its lowercase variant
val lowercase:  string -> Tot string

/// `uppercase`: transform each character to its uppercase variant
val uppercase:  string -> Tot string

/// `index s n`: returns the nth character in `s`
val index: s:string -> n:nat {n < length s} -> Tot char

/// `index_of s c`:
///    The first index of `c` in `s`
///    returns -1 if the char is not found, for compatibility with C
val index_of: string -> char -> Tot int

/// `sub s i len`
///     Second argument is a length, not an index.
///     Returns a substring of length `len` beginning at `i`
val sub: s:string -> i:nat -> l:nat{i + l <= length s} -> Tot (r: string {length r = l})

/// `collect f s`: maps `f` over each character of `s`
///  from left to right, appending and flattening the result
[@@(deprecated "FStar.String.collect can be defined using list_of_string and List.collect")]
val collect: (char -> FStar.All.ML string) -> string -> FStar.All.ML string

/// `substring s i len`
///     A partial variant of `sub s i len` without bounds checks.
///     May fail with index out of bounds
val substring: string -> int -> int -> Ex string

/// `get s i`: Similar to `index` except it may fail
///  if `i` is out of bounds
val get: string -> int -> Ex char


/// Some lemmas (admitted for now as we don't have a model)
val concat_length (s1 s2: string): Lemma
  (ensures length (s1 ^ s2) = length s1 + length s2)

val list_of_concat (s1 s2: string): Lemma
  (ensures list_of_string (s1 ^ s2) == list_of_string s1 @ list_of_string s2)

val index_string_of_list (l:list char) (i : nat{i < List.Tot.length l}) :
  Lemma (
    (**) list_of_string_of_list l; // necessary to get equality between the lengths
    index (string_of_list l) i == List.Tot.index l i)

let index_list_of_string (s:string) (i : nat{i < length s}) :
  Lemma (List.Tot.index (list_of_string s) i == index s i) =
  index_string_of_list (list_of_string s) i;
  string_of_list_of_string s

let concat_injective (s0 s0':string)
                     (s1 s1':string)
  : Lemma
    (s0 ^ s1 == s0' ^ s1' /\
     (length s0 == length s0' \/
      length s1 == length s1') ==>
     s0 == s0' /\ s1 == s1')
  = list_of_concat s0 s1;
    list_of_concat s0' s1';
    append_injective (list_of_string s0)
                     (list_of_string s0')
                     (list_of_string s1)
                     (list_of_string s1');
    string_of_list_of_string s0;
    string_of_list_of_string s0';
    string_of_list_of_string s1;
    string_of_list_of_string s1'
