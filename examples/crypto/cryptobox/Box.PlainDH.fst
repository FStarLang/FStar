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

let ae_key_region = AE.ae_key_region

let get_regionGT = AE.get_regionGT

let get_logGT = AE.get_logGT

let recall_log = AE.recall_log

let empty_log = AE.empty_log
