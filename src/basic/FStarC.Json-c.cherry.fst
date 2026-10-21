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
module FStarC.Json

(* The Cherry implementation.  The OCaml one uses Yojson.Basic, whose
   behaviour this follows.  The parser accepts what Yojson.Basic.from_string
   accepts, including its extensions to JSON: // and /* */ comments, and
   object keys that are identifiers, [A-Za-z_][A-Za-z0-9_]*.  An integer
   must fit in 63 bits, as an OCaml int; floats, NaN and Infinity, which
   have no [json], make the result [None], as do syntax errors.  The printer
   is compact, as Yojson.Basic.to_string, and escapes in the same way. *)

open FStarC.Effect
module I = FStarC.SmallInt
module S = FStarC.String
module U32 = FStar.UInt32

(* In ulib/c/cherry.c. *)
[@@custard_extern "cherry_str_of_byte"]
private assume val of_byte : U32.t -> string

private let byte (s:string) (i:I.t) : int = I.to_int (S.byte_at s i)
private let incr (i:I.t) : I.t = I.(i + one)
private let add (i:I.t) (n:int) : I.t = I.(i + of_int n)
private let slice (s:string) (i j:I.t) : string = S.byte_substring s i j

private let is_digit (c:int) : bool = 48 <= c && c <= 57
private let is_ident_start (c:int) : bool =
  (65 <= c && c <= 90) || (97 <= c && c <= 122) || c = 95
private let is_ident (c:int) : bool = is_ident_start c || is_digit c

(* The UTF-8 encoding of [n] < 0x110000; surrogates are encoded as other
   code points, as Yojson does for a lone low surrogate. *)
private let utf8 (n:int) : string =
  let b (x:int) = of_byte (U32.uint_to_t x) in
  if n < 0x80 then b n
  else if n < 0x800 then b (0xC0 + n / 64) ^ b (0x80 + n % 64)
  else if n < 0x10000 then
    b (0xE0 + n / 4096) ^ b (0x80 + (n / 64) % 64) ^ b (0x80 + n % 64)
  else
    b (0xF0 + n / 262144) ^ b (0x80 + (n / 4096) % 64)
    ^ b (0x80 + (n / 64) % 64) ^ b (0x80 + n % 64)

(* Parsing.  Each function takes the offset to start at and returns the
   offset after what it read, or [None] on an error. *)

(* Skips whitespace and comments. *)
private let rec skip (s:string) (i:I.t) : option I.t =
  let c = byte s i in
  if c = 32 || c = 9 || c = 10 || c = 13 then skip s (incr i)
  else if c = 47 && byte s (incr i) = 47 then skip_line s (add i 2)
  else if c = 47 && byte s (incr i) = 42 then skip_block s (add i 2)
  else Some i
and skip_line (s:string) (i:I.t) : option I.t =
  let c = byte s i in
  if c = -1 then Some i
  else if c = 10 then skip s (incr i)
  else skip_line s (incr i)
and skip_block (s:string) (i:I.t) : option I.t =
  let c = byte s i in
  if c = -1 then None
  else if c = 42 && byte s (incr i) = 47 then skip s (add i 2)
  else skip_block s (incr i)

private let hex_digit (c:int) : int =
  if is_digit c then c - 48
  else if 97 <= c && c <= 102 then c - 87
  else if 65 <= c && c <= 70 then c - 55
  else -1

(* The four hex digits at [i], or -1. *)
private let hex4 (s:string) (i:I.t) : int =
  let d0 = hex_digit (byte s i) in
  let d1 = hex_digit (byte s (add i 1)) in
  let d2 = hex_digit (byte s (add i 2)) in
  let d3 = hex_digit (byte s (add i 3)) in
  if d0 < 0 || d1 < 0 || d2 < 0 || d3 < 0 then -1
  else ((d0 * 16 + d1) * 16 + d2) * 16 + d3

(* The rest of a string literal from [i], after its opening quote; the
   bytes from [start] to [i] are still to be appended to [acc]. *)
private let rec str (s:string) (acc:string) (start i:I.t) : option (string & I.t) =
  let c = byte s i in
  if c = -1 then None
  else if c = 34 then Some (acc ^ slice s start i, incr i)
  else if c = 92 then
    let acc = acc ^ slice s start i in
    let e = byte s (incr i) in
    let simple (r:string) = str s (acc ^ r) (add i 2) (add i 2) in
    if e = 34 then simple "\""
    else if e = 92 then simple "\\"
    else if e = 47 then simple "/"
    else if e = 98 then simple "\b"
    else if e = 102 then simple "\x0c"
    else if e = 110 then simple "\n"
    else if e = 114 then simple "\r"
    else if e = 116 then simple "\t"
    else if e = 117 then
      let n = hex4 s (add i 2) in
      if n < 0 then None
      else if 0xD800 <= n && n < 0xDC00 then
        let lo = if byte s (add i 6) = 92 && byte s (add i 7) = 117 then hex4 s (add i 8) else -1 in
        if 0xDC00 <= lo && lo < 0xE000
        then str s (acc ^ utf8 (0x10000 + (n - 0xD800) * 1024 + (lo - 0xDC00))) (add i 12) (add i 12)
        else None
      else str s (acc ^ utf8 n) (add i 6) (add i 6)
    else None
  else str s acc start (incr i)

private let min_int : int = -4611686018427387904
private let max_int : int = 4611686018427387903

(* The digits of a number from [i], whose value so far is [n]. *)
private let rec digits (s:string) (neg:bool) (n:int) (i:I.t) : option (json & I.t) =
  let c = byte s i in
  if is_digit c then
    let n = n * 10 + (c - 48) in
    if (neg && - n < min_int) || (not neg && n > max_int) then None
    else digits s neg n (incr i)
  else if c = 46 || c = 101 || c = 69 then None (* a float, or an error *)
  else Some (JsonInt (if neg then - n else n), i)

(* A number from [i], after its sign if any. *)
private let number (s:string) (neg:bool) (i:I.t) : option (json & I.t) =
  let c = byte s i in
  if c = 48 then
    let d = byte s (incr i) in
    if is_digit d || d = 46 || d = 101 || d = 69 then None
    else Some (JsonInt 0, incr i)
  else if is_digit c then digits s neg 0 i
  else None

private let keyword (s:string) (i:I.t) (k:string) : bool =
  slice s i (add i (I.to_int (S.byte_length k))) = k

private let rec ident_end (s:string) (i:I.t) : I.t =
  if is_ident (byte s i) then ident_end s (incr i) else i

(* The accumulators of [elements] and [members] have different types. *)
#push-options "--warn_error -290"
(* A value from [i], where there is no whitespace. *)
private let rec value (s:string) (i:I.t) : option (json & I.t) =
  let c = byte s i in
  if c = 110 then (if keyword s i "null" then Some (JsonNull, add i 4) else None)
  else if c = 116 then (if keyword s i "true" then Some (JsonBool true, add i 4) else None)
  else if c = 102 then (if keyword s i "false" then Some (JsonBool false, add i 5) else None)
  else if c = 34 then
    (match str s "" (incr i) (incr i) with
     | Some (r, i) -> Some (JsonStr r, i)
     | None -> None)
  else if c = 45 then number s true (incr i)
  else if is_digit c then number s false i
  else if c = 91 then
    (match skip s (incr i) with
     | Some i when byte s i = 93 -> Some (JsonList [], incr i)
     | Some i -> elements s [] i
     | None -> None)
  else if c = 123 then
    (match skip s (incr i) with
     | Some i when byte s i = 125 -> Some (JsonAssoc [], incr i)
     | Some i -> members s [] i
     | None -> None)
  else None

(* The elements of a list from [i], the earlier ones in [acc] in reverse. *)
and elements (s:string) (acc:list json) (i:I.t) : option (json & I.t) =
  match value s i with
  | None -> None
  | Some (v, i) ->
    match skip s i with
    | None -> None
    | Some i ->
      let c = byte s i in
      if c = 44 then
        (match skip s (incr i) with
         | Some i -> elements s (v :: acc) i
         | None -> None)
      else if c = 93 then Some (JsonList (List.rev (v :: acc)), incr i)
      else None

(* The members of an object from [i], the earlier ones in [acc] in reverse. *)
and members (s:string) (acc:list (string & json)) (i:I.t) : option (json & I.t) =
  let key =
    let c = byte s i in
    if c = 34 then str s "" (incr i) (incr i)
    else if is_ident_start c then
      let j = ident_end s i in Some (slice s i j, j)
    else None in
  match key with
  | None -> None
  | Some (k, i) ->
    match skip s i with
    | Some i when byte s i = 58 ->
      (match skip s (incr i) with
       | None -> None
       | Some i ->
         match value s i with
         | None -> None
         | Some (v, i) ->
           match skip s i with
           | None -> None
           | Some i ->
             let c = byte s i in
             if c = 44 then
               (match skip s (incr i) with
                | Some i -> members s ((k, v) :: acc) i
                | None -> None)
             else if c = 125 then Some (JsonAssoc (List.rev ((k, v) :: acc)), incr i)
             else None)
    | _ -> None

#pop-options

let json_of_string str =
  match skip str I.zero with
  | None -> None
  | Some i ->
    match value str i with
    | None -> None
    | Some (j, i) ->
      match skip str i with
      | Some i when byte str i = -1 -> Some j
      | _ -> None

(* Printing. *)

private let hex (n:int) : string =
  if n < 10 then of_byte (U32.uint_to_t (48 + n)) else of_byte (U32.uint_to_t (87 + n))

(* [acc] followed by the bytes of [s] from [i], escaped; the bytes from
   [start] to [i] are still to be appended. *)
private let rec escape (s:string) (acc:string) (start i:I.t) : string =
  let c = byte s i in
  if c = -1 then acc ^ slice s start i
  else if c = 34 || c = 92 || c < 32 || c = 127 then
    let e =
      if c = 34 then "\\\""
      else if c = 92 then "\\\\"
      else if c = 8 then "\\b"
      else if c = 9 then "\\t"
      else if c = 10 then "\\n"
      else if c = 12 then "\\f"
      else if c = 13 then "\\r"
      else "\\u00" ^ hex (c / 16) ^ hex (c % 16) in
    escape s ((acc ^ slice s start i) ^ e) (incr i) (incr i)
  else escape s acc start (incr i)

private let quoted (acc:string) (s:string) : string =
  escape s (acc ^ "\"") I.zero I.zero ^ "\""

private let rec print (acc:string) (j:json) : string =
  match j with
  | JsonNull -> acc ^ "null"
  | JsonBool b -> acc ^ (if b then "true" else "false")
  | JsonInt n -> acc ^ string_of_int n
  | JsonStr s -> quoted acc s
  | JsonList [] -> acc ^ "[]"
  | JsonList (x :: l) -> print_list (print (acc ^ "[") x) l
  | JsonAssoc [] -> acc ^ "{}"
  | JsonAssoc ((k, v) :: l) -> print_assoc (print (quoted (acc ^ "{") k ^ ":") v) l
and print_list (acc:string) (l:list json) : string =
  match l with
  | [] -> acc ^ "]"
  | x :: l -> print_list (print (acc ^ ",") x) l
and print_assoc (acc:string) (l:list (string & json)) : string =
  match l with
  | [] -> acc ^ "}"
  | (k, v) :: l -> print_assoc (print (quoted (acc ^ ",") k ^ ":") v) l

let string_of_json json = print "" json
