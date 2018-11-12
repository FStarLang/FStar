module EtM.Plain

open Platform.Bytes
open CoreCrypto
open EtM.Ideal

// BEGIN: EtMPlain
abstract type plain = bytes

assume Plain_hasEq: hasEq plain

abstract val repr: p:plain{not conf} -> Tot bytes
let repr p = p

abstract val coerce: r:bytes{not auth} -> Tot plain
let coerce r = r

abstract val length: plain -> Tot nat
let length p = length p
// END: EtMPlain
