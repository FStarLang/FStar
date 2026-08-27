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
open FStarC.Range.Type
open FStar.Char

(* [int_base] is shared with the reflection API (FStar.Stubs.Reflection.V2.Data
also includes FStar.IntegerLiteral), so that the compiler's constants and their
reflected views agree on it. The [include] keeps its constructors accessible as
FStarC.Const.Dec, FStarC.Const.Hex, etc. *)
include FStar.IntegerLiteral

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type signedness = | Unsigned | Signed
[@@ PpxDerivingYoJson; PpxDerivingShow ]
type width = | Int8 | Int16 | Int32 | Int64 | Sizet

(* NB:
    Integer literals are stored as their (mathematical) integer value,
    together with the base they were written in. The base is only kept for
    pretty-printing and extraction: it is *not* part of the meaning of the
    literal, and eq_const below ignores it.
*)

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type sconst =
  | Const_effect
  | Const_unit
  | Const_bool        of bool
  | Const_int         of int & int_base                      (* a mathematical integer, i.e. Prims.int *)
  | Const_machine_int of int & int_base & signedness & width  (* a machine integer, e.g. FStar.UInt8.t *)
  | Const_char        of char (* unicode code point: char in F#, int in OCaml *)
  | Const_real        of FStarC.Real.real
  | Const_string      of string & range                      (* UTF-8 encoded *)
  | Const_range_of                                           (* `range_of` primitive *)
  | Const_set_range_of                                       (* `set_range_of` primitive *)
  | Const_range       of range                               (* not denotable by the programmer *)
  | Const_reify       of option Ident.lid                    (* a coercion from a computation to its underlying repr *)
                                                             (* decorated optionally with the computation effect name *)
  | Const_reflect     of Ident.lid                           (* a coercion from a Tot term to an l-computation type *)

val eq_const (c1 c2 : sconst) : bool

val bounds : signedness -> width -> int & int

val within_bounds : int -> signedness -> width -> bool

(** Render an integer literal in the given base, as it would be written in
source syntax (e.g. [string_of_int_literal 16 Hex = "0x10"]). *)
val string_of_int_literal : int -> int_base -> string

(** Parse an integer literal as produced by the lexer (which may carry a
[0x]/[0o]/[0b] prefix), returning its value and the base it was written in. *)
val parse_int_literal : string -> ML (int & int_base)
