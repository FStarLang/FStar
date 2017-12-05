#light "off"
module FStar.Compiler.Bytes
open FStar.ST
open FStar.All
open FStar.BaseTypes

type array<'a> = 'a[] // JUST FSHARP
type bytes = array<byte>
val length : bytes -> int
val get: bytes -> int -> int
val zero_create : int -> bytes
val of_intarray: int[] -> bytes // JUST FSHARP
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
