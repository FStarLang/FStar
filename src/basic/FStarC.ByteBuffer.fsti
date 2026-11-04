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
module FStarC.ByteBuffer

(* Binary encoding primitives for FStarC.Serialize, with one implementation
   per backend.  Both write exactly the same bytes, so that a file written by
   one can be read by the other.

   Integers are LEB128 varints: seven bits per byte, least significant group
   first, the high bit set on every byte but the last.  A signed integer is
   zigzag-encoded first (0, -1, 1, -2, ... as 0, 1, 2, 3, ...).  [I.t] has 63
   bits in OCaml and 64 in Cherry, so only varints of magnitude below 2^61 are
   portable.  A [Prims.int] in [-2^60, 2^60) is the unsigned varint of twice
   its zigzag encoding; any other is the unsigned varint 1 (non-negative) or
   3 (negative) followed by the length-prefixed decimal digits of its
   absolute value. *)

open FStarC.Effect
module I = FStarC.SmallInt

(* Raised by a reader on a truncated or malformed input. *)
exception Malformed of string

new val writer : Type0

val writer_create : unit -> ML writer
(* A byte, [0 <= b < 256]. *)
val write_byte : writer -> I.t -> ML unit
(* An unsigned varint of a non-negative argument. *)
val write_uvarint : writer -> I.t -> ML unit
(* A zigzag-encoded signed varint. *)
val write_varint : writer -> I.t -> ML unit
(* The bytes of a string, without a length. *)
val write_raw : writer -> string -> ML unit
(* A length-prefixed string. *)
val write_string : writer -> string -> ML unit
val write_int : writer -> int -> ML unit
val writer_size : writer -> ML I.t
val writer_contents : writer -> ML string

new val reader : Type0

(* A reader of the bytes of [s] from offset [off] on. *)
val reader_create : s:string -> off:I.t -> ML reader
val reader_pos : reader -> ML I.t
val read_byte : reader -> ML I.t
val read_uvarint : reader -> ML I.t
val read_varint : reader -> ML I.t
val read_raw : reader -> len:I.t -> ML string
val read_string : reader -> ML string
val read_int : reader -> ML int
