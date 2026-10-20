(*
   Copyright 2008-2023 Microsoft Research

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

module FStarC.BaseTypes

/// This module aggregates commonly used primitive type constants into
/// a single module, providing abbreviations for them.

type char = FStar.Char.char
type float
type double
type byte = FStar.UInt8.t
type int8 = FStar.Int8.t
type uint8 = FStar.UInt8.t
type int16 = FStar.Int16.t
type uint16 = FStar.UInt16.t
type int32 = FStar.Int32.t
type uint32 = FStar.UInt32.t
type int64 = FStar.Int64.t
type uint64 = FStar.UInt64.t

(* A [float] is an IEEE double, as is [FStar.Float64.t]; FStar.Pprint's
   renderer takes the latter. *)
val float64_of_float : float -> FStar.Float64.t
val float_of_float64 : FStar.Float64.t -> float
