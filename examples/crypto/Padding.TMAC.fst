module Padding.TMAC

open Padding
open Padding.Pad

let keysize = BMAC.keysize
let macsize = BMAC.macsize
type key = BMAC.key
type tag = BMAC.tag

opaque type bspec (spec: (text -> Type)) (b:block) =
  (forall (t:text). b = encode t ==> spec t)

opaque type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) =
  k:key{key_prop k == p /\ BMAC.key_prop k == bspec p}

val keygen: p:(text -> Type) -> pkey p
val mac:    p:(text -> Type) -> k:pkey p -> t:text{p t} -> tag
val verify: p:(text -> Type) -> k:pkey p -> t:text -> tag -> b:bool{b ==> p t}

let keygen (spec: text -> Type) =
  let k = BMAC.keygen (bspec spec) in
  assume (key_prop k == spec);
  k

let mac (p:text -> Type) k t = BMAC.mac k (encode t)

let verify k t tag = BMAC.verify k (encode t) tag


