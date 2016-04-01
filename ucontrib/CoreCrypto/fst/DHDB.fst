module DHDB
open Platform.Bytes
open CoreCrypto

type key   = bytes * bytes // p, g
type value = bytes * bool  // q, safe_prime?

assume new type dhdb : Type0

assume val defaultFileName: string
assume val defaultDHPrimeConfidence: int
assume val defaultPQMinLength: nat * nat

assume val create: string -> dhdb
assume val select: dhdb -> key -> option value 
assume val insert: dhdb -> key -> value -> dhdb
assume val remove: dhdb -> key -> dhdb
assume val keys  : dhdb -> list key 
assume val merge : dhdb -> string -> dhdb

assume val dh_check_params: dhdb -> int -> (int * int) -> bytes -> bytes -> option (dhdb * dh_params)
assume val dh_check_element: dh_params -> bytes -> bool
assume val load_default_params: string -> dhdb -> (int * int) -> (dhdb * dh_params)
