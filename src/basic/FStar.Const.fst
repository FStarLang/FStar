﻿(*
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
module FStar.Const
open FStar.Compiler.Effect
module List = FStar.Compiler.List

open FStar.BaseTypes

// IN F*: [@@ PpxDerivingYoJson; PpxDerivingShow ]
type signedness = | Unsigned | Signed
// IN F*: [@@ PpxDerivingYoJson; PpxDerivingShow ]
type width = | Int8 | Int16 | Int32 | Int64 | Sizet

(* NB:
    Const_int (_, None) is not a canonical representation for a mathematical integer
    e.g., you can have both
    Const_int("0x3ffffff", None)
    and
    Const_int("67108863", None)
    which represent the same number
    You should do an "FStar.Compiler.Util.ensure_decimal" on the
    string representation before comparing integer constants.

    eq_const below does that for you
*)

// IN F*: [@@ PpxDerivingYoJson; PpxDerivingShow ]
type sconst =
  | Const_effect
  | Const_unit
  | Const_bool        of bool
  | Const_int         of string * option (signedness * width) (* When None, means "mathematical integer", i.e. Prims.int. *)
  | Const_char        of char (* unicode code point: char in F#, int in OCaml *)
  | Const_real        of string
  | Const_string      of string * FStar.Compiler.Range.range                (* UTF-8 encoded *)
  | Const_range_of                                           (* `range_of` primitive *)
  | Const_set_range_of                                       (* `set_range_of` primitive *)
  | Const_range       of FStar.Compiler.Range.range          (* not denotable by the programmer *)
  | Const_reify       of option Ident.lid                    (* a coercion from a computation to its underlying repr *)
                                                             (* decorated optionally with the computation effect name *)
  | Const_reflect     of Ident.lid                           (* a coercion from a Tot term to an l-computation type *)

let eq_const c1 c2 =
    match c1, c2 with
    | Const_int (s1, o1), Const_int(s2, o2) ->
      FStar.Compiler.Util.ensure_decimal s1 = FStar.Compiler.Util.ensure_decimal s2 &&
      o1=o2
    | Const_string(a, _), Const_string(b, _) -> a=b
    | Const_reflect l1, Const_reflect l2 -> Ident.lid_equals l1 l2
    | Const_reify _, Const_reify _ -> true
    | _ -> c1=c2

open FStar.BigInt
let rec pow2 (x:bigint) : bigint =
  if eq_big_int x zero
  then one
  else mult_big_int two (pow2 (pred_big_int x))


let bounds signedness width =
    let n =
        match width with
        | Int8 -> big_int_of_string "8"
        | Int16 -> big_int_of_string "16"
        | Int32 -> big_int_of_string "32"
        | Int64 -> big_int_of_string "64"
        | Sizet -> big_int_of_string "16"
    in
    let lower, upper =
      match signedness with
      | Unsigned ->
        zero, pred_big_int (pow2 n)
      | Signed ->
        let upper = pow2 (pred_big_int n) in
        minus_big_int upper, pred_big_int upper
    in
    lower, upper

let within_bounds repr signedness width =
  let lower, upper = bounds signedness width in
  let value = big_int_of_string (FStar.Compiler.Util.ensure_decimal repr) in
  le_big_int lower value && le_big_int value upper
