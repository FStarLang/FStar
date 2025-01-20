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
open FStarC.Effect

open FStarC.BigInt
open FStar.Char

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type signedness = | Unsigned | Signed
[@@ PpxDerivingYoJson; PpxDerivingShow ]
type width = | Int8 | Int16 | Int32 | Int64 | Sizet

(* NB:
    Const_int (_, None) is not a canonical representation for a mathematical integer
    e.g., you can have both
    Const_int("0x3ffffff", None)
    and
    Const_int("67108863", None)
    which represent the same number
    You should do an "FStarC.Util.ensure_decimal" on the
    string representation before comparing integer constants.

    eq_const below does that for you
*)

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type sconst =
  | Const_effect
  | Const_unit
  | Const_bool        of bool
  | Const_int         of string & option (signedness & width) (* When None, means "mathematical integer", i.e. Prims.int. *)
  | Const_char        of char (* unicode code point: char in F#, int in OCaml *)
  | Const_real        of string
  | Const_string      of string & FStarC.Range.range                (* UTF-8 encoded *)
  | Const_range_of                                           (* `range_of` primitive *)
  | Const_set_range_of                                       (* `set_range_of` primitive *)
  | Const_range       of FStarC.Range.range                  (* not denotable by the programmer *)
  | Const_reify       of option Ident.lid                    (* a coercion from a computation to its underlying repr *)
                                                             (* decorated optionally with the computation effect name *)
  | Const_reflect     of Ident.lid                           (* a coercion from a Tot term to an l-computation type *)

val eq_const (c1 c2 : sconst) : bool

val pow2 (x:bigint) : bigint

val bounds : signedness -> width -> bigint & bigint

val within_bounds : string -> signedness -> width -> bool
