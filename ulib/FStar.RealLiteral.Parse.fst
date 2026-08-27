(*
   Copyright 2008-2025 Microsoft Research

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
module FStar.RealLiteral.Parse

(* Parsing of real literals. This is separate from FStar.RealLiteral since,
unlike that module, it depends on strings and lists, and FStar.RealLiteral
is used by the (low-level) reflection API. *)

open FStar.Char
open FStar.List.Tot
open FStar.RealLiteral

private let digit_of_char (c : char) : option int =
  match c with
  | '0' -> Some 0
  | '1' -> Some 1
  | '2' -> Some 2
  | '3' -> Some 3
  | '4' -> Some 4
  | '5' -> Some 5
  | '6' -> Some 6
  | '7' -> Some 7
  | '8' -> Some 8
  | '9' -> Some 9
  | _ -> None

(* Splits a list of characters at the first '.', if any. *)
private let rec split_at_dot (cs : list char) : option (list char & list char) =
  match cs with
  | [] -> None
  | '.' :: cs -> Some ([], cs)
  | c :: cs ->
    match split_at_dot cs with
    | None -> None
    | Some (i, f) -> Some (c::i, f)

private let rec digits_of_chars (cs : list char) : option (list int) =
  match cs with
  | [] -> Some []
  | c :: cs ->
    match digit_of_char c, digits_of_chars cs with
    | Some d, Some ds -> Some (d::ds)
    | _ -> None

(* Horner, most significant digit first. *)
private let rec int_of_digits_acc (acc : int) (ds : list int) : Tot int (decreases ds) =
  match ds with
  | [] -> acc
  | d :: ds' -> int_of_digits_acc (acc * 10 + d) ds'

(** Parse a real literal. The accepted syntax is an optional '-' sign,
followed by a non-empty sequence of decimal digits, optionally followed by
a '.' and a (possibly empty) sequence of decimal digits. Returns None if
the string is not a well-formed real literal. *)
let of_string (s : string) : option real_literal =
  let cs = FStar.String.list_of_string s in
  let neg, cs =
    match cs with
    | '-' :: cs -> true, cs
    | _ -> false, cs
  in
  let ipart, fpart =
    match split_at_dot cs with
    | Some (i, f) -> i, f
    | None -> cs, []
  in
  (* The integer part must be present, the fractional part may be empty. *)
  match ipart, digits_of_chars ipart, digits_of_chars fpart with
  | _::_, Some ipart, Some fpart ->
    let m = int_of_digits_acc 0 (ipart @ fpart) in
    Some (mk (if neg then -m else m) (-(length fpart)))
  | _ -> None
