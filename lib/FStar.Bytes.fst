module FStar.Bytes
assume type bytes
assume val length : bytes -> Tot int
assume val get : b:bytes -> pos:nat{pos < length b} -> Tot byte
assume val make : f:(nat -> Tot byte) -> len:nat -> Tot (b:bytes{length b = len})
assume val zero_create : n:nat -> Tot (b:bytes{length b = n})
assume val sub : b:bytes -> s:nat{s < length b} -> e:nat{e < length b /\ s <= e} -> Tot (sub:bytes{length sub = e - s + 1})
assume val set : b:bytes -> n:nat{n < length b} -> byte -> unit
assume val string_as_unicode_bytes : string -> bytes
assume val utf8_bytes_as_string : bytes -> string
assume val unicode_bytes_as_string : bytes -> string
assume val string_as_utf8_bytes : string -> bytes
assume val append : bytes -> bytes -> bytes

