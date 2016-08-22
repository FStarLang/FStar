module MtE.Plain

open Platform.Bytes
open CoreCrypto

abstract type plain = bytes

assume Plain_hasEq: hasEq plain

assume val ind_cpa: bool

val repr: p:plain{~ind_cpa} -> Tot bytes
let repr p = p

val coerce: r:bytes{~ind_cpa} -> Tot plain
let coerce r = r

val length: plain -> Tot nat
let length p = length p
