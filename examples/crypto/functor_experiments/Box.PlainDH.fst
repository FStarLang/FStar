(**
   TODO: Documentation.
*)
module Box.PlainDH

open CoreCrypto
open Platform.Bytes
open Box.Flags
open Box.Indexing
open Box.AE

type key = AE.key

let ae_key_get_index = AE.get_index

let keygen = AE.keygen

let coerce_key = AE.coerce_key

let leak_key = AE.leak_key
