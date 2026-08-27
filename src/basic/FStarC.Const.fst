(*
   Copyright 2008-2020 Microsoft Research

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
module FStarC.Const
open FStarC.Range.Type
open FStarC.Effect

open FStar.Char

include FStar.IntegerLiteral

module BU = FStarC.Util

let eq_const c1 c2 =
    match c1, c2 with
    (* The base an integer literal was written in is not semantically
       relevant: 0x10 and 16 are the same constant. *)
    | Const_int (v1, _), Const_int (v2, _) -> v1 = v2
    | Const_machine_int (v1, _, s1, w1), Const_machine_int (v2, _, s2, w2) ->
      v1 = v2 && s1 = s2 && w1 = w2
    | Const_string(a, _), Const_string(b, _) -> a=b
    | Const_real r1, Const_real r2 -> Real.cmp r1 r2 = FStarC.Order.Eq
    | Const_reflect l1, Const_reflect l2 -> Ident.lid_equals l1 l2
    | Const_reify _, Const_reify _ -> true
    | _ -> c1=c2

let rec pow2 (x : int) : int =
  if x = 0
  then 1
  else 2 * pow2 (x - 1)

let bounds signedness width =
    let n =
        match width with
        | Int8  -> 8
        | Int16 -> 16
        | Int32 -> 32
        | Int64 -> 64
        | Sizet -> 16
    in
    let lower, upper =
      match signedness with
      | Unsigned ->
        0, pow2 n - 1
      | Signed ->
        let upper = pow2 (n - 1) in
        - upper, upper - 1
    in
    lower, upper

let within_bounds value signedness width =
  let lower, upper = bounds signedness width in
  lower <= value && value <= upper

let digit_char (d:int) : string =
  if      d = 0  then "0" else if d = 1  then "1"
  else if d = 2  then "2" else if d = 3  then "3"
  else if d = 4  then "4" else if d = 5  then "5"
  else if d = 6  then "6" else if d = 7  then "7"
  else if d = 8  then "8" else if d = 9  then "9"
  else if d = 10 then "a" else if d = 11 then "b"
  else if d = 12 then "c" else if d = 13 then "d"
  else if d = 14 then "e" else "f"

let string_of_int_literal (i:int) (b:int_base) : string =
  match b with
  | Dec -> Prims.string_of_int i
  | _ ->
    let base, prefix =
      match b with
      | Hex -> 16, "0x"
      | Oct -> 8,  "0o"
      | Bin -> 2,  "0b"
      | Dec -> 10, "" (* unreachable *)
    in
    let sign, n = if i < 0 then "-", -i else "", i in
    let rec go (n:int) (acc:string) : string =
      if n = 0 then acc else go (n / base) (digit_char (n % base) ^ acc)
    in
    sign ^ prefix ^ (if n = 0 then "0" else go n "")

let parse_int_literal (s:string) : ML (int & int_base) =
  let s' = if BU.starts_with s "-" then BU.substring_from s 1 else s in
  let b =
    if      BU.starts_with s' "0x" || BU.starts_with s' "0X" then Hex
    else if BU.starts_with s' "0o" || BU.starts_with s' "0O" then Oct
    else if BU.starts_with s' "0b" || BU.starts_with s' "0B" then Bin
    else Dec
  in
  BU.int_of_string s, b
