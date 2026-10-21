(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.String

(* The Cherry implementation.  A string is UTF-8 and a [char] is a code
   point, as in the OCaml build.  The code-point functions walk the bytes;
   malformed UTF-8 decodes to U+FFFD.  Results are built by appending to a
   string nobody else holds, which Cherry does in place. *)

open FStarC.Effect
open FStar.Char
module I = FStarC.SmallInt
module U32 = FStar.UInt32
module S = FStar.String

(* In ulib/c/cherry.c. *)
[@@custard_extern "cherry_str_size64"]
private assume val size64 : string -> I.t
[@@custard_extern "cherry_str_byte_at64"]
private assume val byte_at64 : string -> I.t -> I.t
[@@custard_extern "cherry_str_slice64"]
private assume val slice64 : string -> I.t -> I.t -> string
[@@custard_extern "cherry_str_of_byte"]
private assume val of_byte : U32.t -> string
[@@custard_extern "cherry_str_lowercase_ascii"]
private assume val lowercase_ascii : string -> string
[@@custard_extern "cherry_str_uppercase_ascii"]
private assume val uppercase_ascii : string -> string
[@@custard_extern "cherry_str_escaped"]
private assume val escaped_bytes : string -> string

let byte_length s = size64 s

(* Recursion bounds: lengths are not negative. *)
private let fuel_of (x:I.t) : nat = let k = I.to_int x in if k < 0 then 0 else k

let byte_at s i = byte_at64 s i

(* The code point, or U+FFFD if [n] is a surrogate or out of range. *)
private let char_of_int (n:int) : char =
  if (0 <= n && n < 0xd7ff) || (0xe000 <= n && n <= 0x10ffff)
  then char_of_u32 (U32.uint_to_t n)
  else char_of_u32 0xFFFDul

(* The payload of the continuation byte at [i], or -1 if it is not one. *)
private let cont (s:string) (i:I.t) : int =
  let b = I.to_int (byte_at s i) in
  if 0x80 <= b && b < 0xC0 then b - 0x80 else -1

private let decode (s:string) (i:I.t) : int =
  let b = I.to_int (byte_at s i) in
  if b < 0x80 then b
  else if b < 0xC2 then 0xFFFD
  else if b < 0xE0 then
    let c1 = cont s I.(i + one) in
    if c1 < 0 then 0xFFFD else (b - 0xC0) * 64 + c1
  else if b < 0xF0 then
    let c1 = cont s I.(i + one) in
    let c2 = cont s I.(i + of_int 2) in
    if c1 < 0 || c2 < 0 then 0xFFFD else (b - 0xE0) * 4096 + c1 * 64 + c2
  else if b < 0xF5 then
    let c1 = cont s I.(i + one) in
    let c2 = cont s I.(i + of_int 2) in
    let c3 = cont s I.(i + of_int 3) in
    if c1 < 0 || c2 < 0 || c3 < 0 then 0xFFFD
    else (b - 0xF0) * 262144 + c1 * 4096 + c2 * 64 + c3
  else 0xFFFD

let code_point_at s i = I.of_int (decode s i)

let next_code_point s i =
  let b = I.to_int (byte_at s i) in
  let w = if b < 0x80 then 1 else if b < 0xE0 then 2 else if b < 0xF0 then 3 else 4 in
  let j = I.(i + of_int w) in
  let n = byte_length s in
  if I.(j < n) then j else n

let byte_substring s i j = slice64 s i j

(* Whether [t] occurs in [s] at offset [i]: compares [t]'s bytes from [k] on.
   The fuel bounds the recursion; it is never what stops it. *)
private
let rec occurs_at (s t:string) (i k tlen:I.t) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 || I.(k >= tlen) then true
  else if byte_at s I.(i + k) = byte_at t k then occurs_at s t i I.(k + one) tlen (fuel - 1)
  else false

(* The pieces of [s] from [start] on, the earlier ones in [acc] in reverse.
   [i] is where to look for [t] next. *)
private
let rec split_from (s t:string) (slen tlen start i:I.t) (fuel:nat) (acc:list string)
  : Tot (list string) (decreases fuel)
  = if fuel = 0 || I.(i + tlen > slen) then
      List.Tot.rev (byte_substring s start slen :: acc)
    else if occurs_at s t i I.zero tlen (fuel_of tlen) then
      let j = I.(i + tlen) in
      split_from s t slen tlen j j (fuel - 1) (byte_substring s start i :: acc)
    else
      split_from s t slen tlen start I.(i + one) (fuel - 1) acc

let split_on_string s sep =
  let slen = byte_length s in
  let tlen = byte_length sep in
  if slen = I.zero then []
  else if tlen = I.zero then [s]
  else split_from s sep slen tlen I.zero I.zero (fuel_of slen + 1) []

(* As [BatUTF8.init], a negative length makes the empty string. *)
let make i c = if i <= 0 then "" else S.make i c

(* Splits on each separator in turn.  As [split_on_string] has nothing for
   an empty piece, a separator drops the empty pieces left by those before
   it. *)
let split seps s =
  let rec go (acc:list string) (seps:list char) : Tot (list string) (decreases seps) =
    match seps with
    | [] -> acc
    | sep :: seps ->
      let usep = S.make 1 sep in
      go (List.Tot.concatMap (fun x -> split_on_string x usep) acc) seps
  in
  go [s] seps

let strcat s1 s2 = Prims.strcat s1 s2

private let rec concat_onto (sep:string) (acc:string) (l:list string) : Tot string (decreases l) =
  match l with
  | [] -> acc
  | x :: t -> concat_onto sep (Prims.strcat (Prims.strcat acc sep) x) t

let concat sep l =
  match l with
  | [] -> ""
  | x :: t -> concat_onto sep (Prims.strcat "" x) t

let compare s1 s2 = S.compare s1 s2

let strlen s = S.length s

let length s = S.length s

let lowercase s = lowercase_ascii s

let uppercase s = uppercase_ascii s

let escaped s = escaped_bytes s

(* A single byte, as OCaml's [Char.chr]: a code point from 128 to 255 makes
   a string that is not UTF-8.  One above 255 is outside its domain (OCaml
   raises Invalid_argument); Cherry's debug mode reports it. *)
#push-options "--admit_smt_queries true"
let string_of_char c =
  let n = U32.v (u32_of_char c) in
  if n < 256 then of_byte (u32_of_char c) else false_elim ()
#pop-options

let substring s i j =
  if i < 0 || j < 0 || i + j > S.length s then failwith "String.substring: index out of bounds"
  else S.sub s i j

let get s i =
  if i < 0 || i >= S.length s then failwith "String.get: index out of bounds"
  else S.index s i

private let rec collect_from (f:char -> ML string) (s:string) (n i:I.t) (acc:string) (fuel:nat)
  : ML string =
  if fuel = 0 || I.(i >= n) then acc
  else
    let c = char_of_int (decode s i) in
    let r = f c in
    collect_from f s n (next_code_point s i) (Prims.strcat acc r) (fuel - 1)

let collect f s =
  let n = byte_length s in
  collect_from f s n I.zero "" (fuel_of n)

private let rec index_of_from (s:string) (c:int) (n i:I.t) (k:int) (fuel:nat)
  : Tot int (decreases fuel) =
  if fuel = 0 || I.(i >= n) then -1
  else if decode s i = c then k
  else index_of_from s c n (next_code_point s i) (k + 1) (fuel - 1)

let index_of s c =
  let n = byte_length s in
  index_of_from s (U32.v (u32_of_char c)) n I.zero 0 (fuel_of n)

let index s i = get s i

private let rec chars_from (s:string) (n i:I.t) (acc:list char) (fuel:nat)
  : Tot (list char) (decreases fuel) =
  if fuel = 0 || I.(i >= n) then List.Tot.rev acc
  else chars_from s n (next_code_point s i) (char_of_int (decode s i) :: acc) (fuel - 1)

let list_of_string s =
  let n = byte_length s in
  chars_from s n I.zero [] (fuel_of n)

private let rec string_onto (acc:string) (l:list char) : Tot string (decreases l) =
  match l with
  | [] -> acc
  | c :: t -> string_onto (Prims.strcat acc (S.make 1 c)) t

let string_of_list l = string_onto "" l

let ( ^ ) s1 s2 = Prims.strcat s1 s2
