module EtM.Plain

open Platform.Bytes
open CoreCrypto
open EtM.Ideal

abstract type plain = bytes

assume Plain_hasEq: hasEq plain

//assume val ind_cpa: bool

val repr: p:plain{~ind_cpa} -> Tot bytes
let repr p = p

val coerce: r:bytes{(not ind_cpa) || (not uf_cma)} -> Tot plain
let coerce r = r

val length: plain -> Tot nat
let length p = length p
