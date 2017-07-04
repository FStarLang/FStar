module EtM.Plain

open Platform.Bytes
open CoreCrypto
open EtM.Ideal

abstract type plain = bytes

assume Plain_hasEq: hasEq plain

val repr: p:plain{not conf} -> Tot bytes
let repr p = p

val coerce: r:bytes{not auth} -> Tot plain
let coerce r = r

val length: plain -> Tot nat
let length p = length p
