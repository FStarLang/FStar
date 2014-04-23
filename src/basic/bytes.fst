module Microsoft.FStar.Bytes

type bytes
assume val length : bytes -> int
assume val get: bytes -> int -> int
assume val zero_create : int -> bytes
assume val of_intarray: array<int> -> bytes
assume val string_as_unicode_bytes: string -> bytes
assume val unicode_bytes_as_string: bytes -> string
assume val utf8_bytes_as_string: bytes -> string
assume val append: bytes -> bytes -> bytes
assume val make: (int -> int) -> int -> bytes
assume val for_range: bytes -> int -> int -> (int -> unit) -> unit

type bytebuf
assume val create: int -> bytebuf
assume val close : bytebuf -> bytes
assume val emit_int_as_byte: bytebuf -> int -> unit
assume val emit_bytes: bytebuf -> bytes -> unit
