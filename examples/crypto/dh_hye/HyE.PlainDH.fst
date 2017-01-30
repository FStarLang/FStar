(**
   TODO: Documentation.
*)
module HyE.PlainDH

open CoreCrypto
open Platform.Bytes
open HyE.Flags
open HyE.Indexing
open HyE.AE

type key = AE.key

let keygen = AE.keygen

let coerce_key = AE.coerce_key

let leak_key = AE.leak_key
