#light "off"
module FStar.Bytes
open FStar.All
type bytes = (* abstract *)
    byte[]   (* except in F# *)
val length : bytes -> Prims.int
val get: bytes -> Prims.int -> int
val zero_create : int -> bytes
val of_intarray: int[] -> bytes
val string_as_unicode_bytes: string -> bytes
val unicode_bytes_as_string: bytes -> string
val utf8_bytes_as_string: bytes -> string
val append: bytes -> bytes -> bytes
val make: (Prims.int -> int) -> Prims.int -> bytes

type bytebuf = (* abstract *)
    { mutable bbArray: bytes;  (* except in F# *)
      mutable bbCurrent: int }
val create: int -> bytebuf
val close : bytebuf -> bytes
val emit_int_as_byte: bytebuf -> Prims.int -> unit
val emit_bytes: bytebuf -> bytes -> unit

val f_encode: (byte -> string) -> bytes -> string
