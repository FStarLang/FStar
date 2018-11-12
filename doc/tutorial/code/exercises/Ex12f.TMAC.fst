module Ex12f.TMAC

open FStar.Seq

open Ex12.Pad 

module BMAC = Ex12.BMAC


let keysize = BMAC.keysize
let macsize = BMAC.macsize
type key = BMAC.key
type tag = BMAC.tag

type bspec (spec: (text -> Type)) (b:block) = 
  (forall (t:text). equal b (encode t) ==> spec t)

assume type key_prop : key -> text -> Type

type pkey (p:(text -> Type)) = 
  k:key{key_prop k == p /\ BMAC.key_prop k == bspec p}
  
// BEGIN: TMACEx
val keygen: p:(text -> Type) -> pkey p
val mac:    p:(text -> Type) -> k:pkey p -> t:text{p t} -> tag
val verify: p:(text -> Type) -> k:pkey p -> t:text -> tag -> b:bool{b ==> p t}
(*implement these functions*)
// END: TMACEx
