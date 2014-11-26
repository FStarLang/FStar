module Pad
open Array

type bytes = seq byte (* concrete byte arrays *) 
type nbytes (n:nat) = b:bytes{length b == n} (* fixed-length bytes *)

let blocksize = 32 
type block = nbytes blocksize
type text = b:bytes {op_LessThan (length b) blocksize}

assume val pad: n:nat {op_LessThan n blocksize} -> Tot (nbytes (n+1))

// let pad p = Array.create p (byte(p-1))  
(* pad 1 = [| 0 |]; pad 2 = [| 1; 1 |]; ... *)


val encode: a: text -> 
  Tot (b: block { b = append a (pad (blocksize - length a)) })

let encode a = append a (pad (blocksize - length a))

val inj: a: text -> b: text -> u:unit 
  { encode a = encode b ==> a = b }

let inj a b = ()

let decode (b:block) = 
  let padsize = Array.index b (blocksize - 1) + 1 in
  if op_LessThan padsize blocksize then 
    let (plain,padding) = split (blocksize - padsize) b in
    if padding = pad padsize
    then 
      (assert(b = encode plain); Some(plain))
    else None   
  else None


module BMAC
open Pad 

let keysize = 16 (* these are the sizes for SHA1 *) 
let macsize = 20  
type key = nbytes keysize
type tag = nbytes macsize

opaque type key_prop : key -> block -> Type
type pkey (p:(block -> Type)) = k:key{key_prop k == p}

assume val keygen: p:(block -> Type) -> pkey p
assume val mac:    k:key -> t:block{key_prop k t} -> tag
assume val verify: k:key -> t:block -> tag -> b:bool{b ==> key_prop k t}

module TMAC
open Pad 

let keysize = BMAC.keysize
let macsize = BMAC.macsize
type key = BMAC.key
type tag = BMAC.tag

opaque type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = k:key{key_prop k == p}

val keygen: p:(text -> Type) -> pkey p
val mac:    k:key -> t:text{key_prop k t} -> tag
val verify: k:key -> t:text -> tag -> b:bool{b ==> key_prop k t}

type bspec (spec: (text -> Type)) (b:block) = 
  (exists (t:text). spec t /\ block = encode t)

let keygen p spec = 
  let k = BMAC.keygen (bspec spec) in
  assume (key_prop k spec);
  k

let mac k t = BMAC.mac k (encode t)
let verify k t tag = BMAC.mac k (encode t) tag

