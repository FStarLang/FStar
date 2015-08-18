module DHDB
open Platform.Bytes
open CoreCrypto

type Key   = bytes * bytes // p, g
type Value = bytes * bool  // q, safe_prime?

type dhdb

assume val defaultFileName: string
assume val defaultDHPrimeConfidence: int
assume val defaultPQMinLength: nat * nat

assume val create: string -> dhdb
assume val select: dhdb -> Key -> option Value 
assume val insert: dhdb -> Key -> Value -> dhdb
assume val remove: dhdb -> Key -> dhdb
assume val keys  : dhdb -> list Key 
assume val merge : dhdb -> string -> dhdb

assume val dh_check_params: dhdb -> int -> (int * int) -> bytes -> bytes -> option (dhdb * dh_params)
assume val dh_check_element: dh_params -> bytes -> bool
assume val load_default_params: string -> dhdb -> (int * int) -> (dhdb * dh_params)