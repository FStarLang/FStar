(*
   Copyright 2016 Microsoft Research

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
module FStarC.Bytes
open FStarC.Effect
open FStarC.BaseTypes

type bytes = FStarC.Array.array byte
val length : bytes -> int
val get: bytes -> int -> int
val zero_create : int -> bytes
val string_as_unicode_bytes: string -> bytes
val unicode_bytes_as_string: bytes -> string
val utf8_bytes_as_string: bytes -> string
val append: bytes -> bytes -> bytes
val make: (int -> int) -> int -> bytes

type bytebuf
val create: int -> bytebuf
val close : bytebuf -> bytes
val emit_int_as_byte: bytebuf -> int -> unit
val emit_bytes: bytebuf -> bytes -> unit

val f_encode: (byte -> string) -> bytes -> string
