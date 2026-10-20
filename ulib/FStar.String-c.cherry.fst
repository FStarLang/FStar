(*
   Copyright 2026 Microsoft Research

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

(* The implementation used by the Cherry backend.  A string is UTF-8 and a
   [char] is a code point, as in the OCaml build.  The functions over code
   points walk the bytes; malformed UTF-8 decodes to U+FFFD.  The ones the
   runtime has ([length], [make], [index], [sub], [compare], the case
   mappings) are its, in ulib/c/cherry.c.  Results are built by appending to
   a string nobody else holds, which Cherry does in place. *)

open FStar.List.Tot
open FStar.Char
module U32 = FStar.UInt32

[@@custard_extern "cherry_str_byte_size"]
private assume val byte_size : string -> nat
[@@custard_extern "cherry_str_byte_at"]
private assume val byte_at : string -> int -> U32.t
[@@custard_extern "cherry_str_byte_sub"]
private assume val byte_sub : string -> int -> int -> string
[@@custard_extern "cherry_str_make"]
private assume val c_make : nat -> char -> string

(* The byte at [i], or 256 past the end. *)
private let byte (s:string) (n i:int) : int =
  if 0 <= i && i < n then U32.v (byte_at s i) else 256

(* The code point, or U+FFFD if [n] is a surrogate or out of range. *)
private let to_char (n:int) : char =
  if (0 <= n && n < 0xd7ff) || (0xe000 <= n && n <= 0x10ffff)
  then char_of_u32 (U32.uint_to_t n)
  else char_of_u32 0xFFFDul

(* The payload of the continuation byte at [i], or -1 if it is not one. *)
private let cont (s:string) (n i:int) : int =
  let b = byte s n i in
  if 0x80 <= b && b < 0xC0 then b - 0x80 else -1

(* The code point at byte [i] of [s], whose size is [n]. *)
private let decode (s:string) (n i:int) : int =
  let b = byte s n i in
  if b < 0x80 then b
  else if b < 0xC2 then 0xFFFD
  else if b < 0xE0 then
    let c1 = cont s n (i + 1) in
    if c1 < 0 then 0xFFFD else (b - 0xC0) * 64 + c1
  else if b < 0xF0 then
    let c1 = cont s n (i + 1) in
    let c2 = cont s n (i + 2) in
    if c1 < 0 || c2 < 0 then 0xFFFD else (b - 0xE0) * 4096 + c1 * 64 + c2
  else if b < 0xF5 then
    let c1 = cont s n (i + 1) in
    let c2 = cont s n (i + 2) in
    let c3 = cont s n (i + 3) in
    if c1 < 0 || c2 < 0 || c3 < 0 then 0xFFFD
    else (b - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3
  else 0xFFFD

(* The size of the code point whose first byte is [b]. *)
private let width (b:int) : pos =
  if b < 0x80 then 1 else if b < 0xE0 then 2 else if b < 0xF0 then 3 else 4

(* Each loop below takes one step per code point from byte [i] on; the fuel,
   the size of the string, bounds the recursion but never stops it. *)
private
let rec chars_from (s:string) (n i:int) (fuel:nat) (acc:list char)
  : Tot (list char) (decreases fuel) =
  if fuel = 0 || i >= n then rev acc
  else chars_from s n (i + width (byte s n i)) (fuel - 1) (to_char (decode s n i) :: acc)

[@@"opaque_to_smt"]
let list_of_string s =
  let n = byte_size s in
  chars_from s n 0 n []

private let rec chars_onto (acc:string) (l:list char) : Tot string (decreases l) =
  match l with
  | [] -> acc
  | c :: l -> chars_onto (acc ^ c_make 1 c) l

[@@"opaque_to_smt"]
let string_of_list l = chars_onto "" l

let string_of_list_of_string s = admit ()

let list_of_string_of_list (l:list char)
  : Lemma (list_of_string (string_of_list l) == l) = admit ()

[@@custard_extern "cherry_str_length"]
private assume val c_length : s:string -> l:nat{l = strlen s}

[@@"opaque_to_smt"]
let length s = c_length s


[@@custard_extern "cherry_str_make"]
private assume val c_make' : l:nat -> char -> s:string{length s = l}

let make l c = c_make' l c

(* The pieces of [s] between the code points [sep], the earlier ones in
   [acc] in reverse; the current piece starts at byte [start]. *)
private
let rec split_from (s:string) (n i start sep:int) (fuel:nat) (acc:list string)
  : Tot (list string) (decreases fuel) =
  if fuel = 0 || i >= n then rev (byte_sub s start (n - start) :: acc)
  else
    let j = i + width (byte s n i) in
    let j = if j > n then n else j in
    if decode s n i = sep
    then split_from s n j j sep (fuel - 1) (byte_sub s start (i - start) :: acc)
    else split_from s n j start sep (fuel - 1) acc

(* Splits on each separator in turn.  Like the pre-2.11 [BatString.nsplit]
   the OCaml build uses, an empty piece splits into no pieces at all. *)
let split seps s =
  let split1 (sep:char) (x:string) : list string =
    if x = "" then []
    else let n = byte_size x in split_from x n 0 0 (U32.v (u32_of_char sep)) n [] in
  let rec go (acc:list string) (seps:list char) : Tot (list string) (decreases seps) =
    match seps with
    | [] -> acc
    | sep :: seps -> go (concatMap (split1 sep) acc) seps
  in
  go [s] seps

private let rec concat_onto (sep:string) (acc:string) (l:list string) : Tot string (decreases l) =
  match l with
  | [] -> acc
  | x :: t -> concat_onto sep ((acc ^ sep) ^ x) t

let concat sep l =
  match l with
  | [] -> ""
  | x :: t -> concat_onto sep ("" ^ x) t

[@@custard_extern "cherry_str_compare"]
private assume val c_compare : string -> string -> int

let compare s1 s2 = c_compare s1 s2

[@@custard_extern "cherry_str_lowercase_ascii"]
private assume val c_lowercase : string -> string

let lowercase s = c_lowercase s

[@@custard_extern "cherry_str_uppercase_ascii"]
private assume val c_uppercase : string -> string

let uppercase s = c_uppercase s

[@@custard_extern "cherry_str_index"]
private assume val c_index : s:string -> n:nat{n < length s} -> char

let index s n = c_index s n

(* The index of the first code point [c] from byte [i] on, where the code
   point index is [k]. *)
private
let rec index_from (s:string) (n i k c:int) (fuel:nat) : Tot int (decreases fuel) =
  if fuel = 0 || i >= n then -1
  else if decode s n i = c then k
  else index_from s n (i + width (byte s n i)) (k + 1) c (fuel - 1)

let index_of s c =
  let n = byte_size s in
  index_from s n 0 0 (U32.v (u32_of_char c)) n

[@@custard_extern "cherry_str_sub"]
private assume val c_sub : s:string -> i:nat -> l:nat{i + l <= length s} -> r:string{length r = l}

let sub s i l = c_sub s i l

let collect f s =
  let n = byte_size s in
  let rec go (i:int) (acc:string) : FStar.All.ML string =
    if i >= n then acc
    else go (i + width (byte s n i)) (acc ^ f (to_char (decode s n i)))
  in
  go 0 ""

let substring s i j =
  if i < 0 || j < 0 || i + j > length s
  then FStar.All.failwith "FStar.String.substring: out of bounds"
  else c_sub s i j

let get s i =
  if i < 0 || i >= length s
  then FStar.All.failwith "FStar.String.get: out of bounds"
  else c_index s i

let concat_length _ _ = admit ()

let list_of_concat _ _ = admit ()

#push-options "--admit_smt_queries true"
let index_string_of_list _ _ = admit ()
#pop-options
