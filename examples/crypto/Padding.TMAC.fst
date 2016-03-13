module Padding.TMAC

open Padding.Pad
open Padding.BMAC

let keysize = BMAC.keysize
let macsize = BMAC.macsize

type key = BMAC.key
type tag = BMAC.tag
  
opaque type bspec (spec:text -> Type) (b:block) = 
  forall (t:text). b = encode t ==> spec t

opaque new type key_prop : key -> text -> Type

type pkey (p:text -> Type) =
  k:key{key_prop k == p /\ (forall b. BMAC.key_prop k b == bspec p b)}

val keygen: p:(text -> Type) -> pkey p
val mac:    p:(text -> Type) -> k:pkey p -> t:text{p t} -> tag
val verify: p:(text -> Type) -> k:pkey p -> t:text -> tag -> b:bool{b ==> p t}

let keygen (p:text -> Type) = 
  let k = BMAC.keygen (bspec p) in
  assume (key_prop k == p);
  k

let mac (p:text -> Type) k t = 
  BMAC.mac k (encode t)

let verify k t tag = 
  BMAC.verify k (encode t) tag
