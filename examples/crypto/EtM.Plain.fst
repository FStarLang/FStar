module EtM.Plain

open Platform.Bytes
open CoreCrypto
open EtM.Ideal

abstract 
type plain : eqtype = bytes

abstract
let reveal (p:plain) : GTot bytes = p

abstract
let hide (b:bytes) : GTot plain = b

let reveal_hide (p:plain) 
  : Lemma (hide (reveal p) == p)
          [SMTPat (reveal p)]
  = ()

let hide_reveal (b:bytes) 
  : Lemma (reveal (hide b) == b)
          [SMTPat (hide b)]
  = ()

abstract
let repr (p:plain{not conf}) 
  : (b:bytes{b == reveal p}) 
  = p

abstract
let coerce (r:bytes{not auth}) 
  : (p:plain{p == hide r}) 
  = r

module B = Platform.Bytes
abstract
let length (p:plain) 
  : (n:nat{n = B.length (reveal p)})
  = B.length p
