module Ex12g.TMAC2

open FStar.Seq
open Ex12.Pad 

module BMAC = Ex12.BMAC

type text2 = b:bytes { length b <=  blocksize } 

let keysize = op_Multiply 2 BMAC.keysize
let macsize = BMAC.macsize
noeq type key = | Keys: k0:BMAC.key -> k1:BMAC.key -> key
type tag = BMAC.tag

type bspec0 (spec: (text2 -> Type)) (b:block) =
  (forall (t:text). equal b (encode t) ==> spec t)

type bspec1 (spec: (text2 -> Type)) (b:block) = 
  spec b

assume type key_prop : key -> text2 -> Type

type pkey (p:(text2 -> Type)) = 
  k:key{ key_prop k == p
      /\ BMAC.key_prop (Keys?.k0 k) == bspec0 p
      /\ BMAC.key_prop (Keys?.k1 k) == bspec1 p }

val keygen: p:(text2 -> Type) -> pkey p
val mac:    p:(text2 -> Type) -> k:pkey p -> t:text2{p  t} -> tag
val verify: p:(text2 -> Type) -> k:pkey p -> t:text2 -> tag -> b:bool{b ==> p t}

(* not verified yet: *)
let keygen (spec: text2 -> Type) = 
  let k0 = BMAC.keygen (bspec0 spec) in
  let k1 = BMAC.keygen (bspec1 spec) in
  let k = Keys k0 k1 in
  assert (BMAC.key_prop k0 == bspec0 spec);
  assert (BMAC.key_prop k1 == bspec1 spec);
  assume (key_prop k == spec);
  k
 
(*implement functions mac and verify*)
