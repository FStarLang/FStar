module Padding.MAC2

open FStar.Seq
open FStar.SeqProperties

open Padding.Pad
open Padding.BMAC

type text2 = b:bytes { length b <=  blocksize }

let keysize = 2 * BMAC.keysize
let macsize = BMAC.macsize

type key = | Keys: k0:BMAC.key -> k1:BMAC.key -> key
type tag = BMAC.tag

opaque type bspec0 (spec:text2 -> Type) (b:block) =
  forall (t:text). b = encode t ==> spec t

opaque type bspec1 (spec:text2 -> Type) (b:block) =
  spec b

opaque new type key_prop: key -> text2 -> Type

type pkey (p:text2 -> Type) =
  k:key{ key_prop k == p
      /\ (forall b. BMAC.key_prop (Keys.k0 k) b == bspec0 p b) 
      /\ (forall b. BMAC.key_prop (Keys.k1 k) b == bspec1 p b) }

val keygen: p:(text2 -> Type) -> pkey p
val mac:    p:(text2 -> Type) -> k:pkey p -> t:text2{p t} -> tag
val verify: p:(text2 -> Type) -> k:pkey p -> t:text2 -> tag -> b:bool{b ==> p t}

let keygen (p:text2 -> Type) =
  let k0 = BMAC.keygen (bspec0 p) in
  let k1 = BMAC.keygen p in
  let k = Keys k0 k1 in
  assume (key_prop k == p);
  k

let mac (p:text2 -> Type) k t =
  if length t < blocksize
  then BMAC.mac k.k0 (encode t)
  else BMAC.mac k.k1 t

let verify (p:text2 -> Type) k t tag =
  if length t < blocksize
  then BMAC.verify k.k0 (encode t) tag
  else BMAC.verify k.k1 t tag
