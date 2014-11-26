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

assume val tonat: b:uint8 -> nat

val decode: b:block -> option (t:text { b = encode t })
let decode (b:block) = 
  let padsize = tonat(Array.index b (blocksize - 1)) + 1 in
  if op_LessThan padsize blocksize then 
    let (plain,padding) = split b (blocksize - padsize) in
    if padding = pad padsize
    then Some plain
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

// assume type bspec: (text -> Type) -> (block -> Type)

type bspec (spec: (text -> Type)) (b:block) = 
  (exists (t:text).spec t /\ b = encode t)

opaque type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = 
  k:key{key_prop k == p /\ BMAC.key_prop k == bspec p}

val keygen: p:(text -> Type) -> pkey p
val mac:    k:key -> t:text{key_prop k t} -> tag
val verify: k:key -> t:text -> tag -> b:bool{b ==> key_prop k t}

(*
let keygen (spec: text -> Type) = 
  let k = BMAC.keygen (bspec spec) in
  not typing:  assume (key_prop k spec);
  k
*)

let mac k t = BMAC.mac k (encode t)
let verify k t tag = BMAC.verify k (encode t) tag


module MAC2
open Array
open Pad 

type text2 = b:bytes { op_LessThan (length b) (blocksize + 1) } 

let keysize = 2 * BMAC.keysize
let macsize = BMAC.macsize
type key = BMAC.key * BMAC.key
type tag = BMAC.tag

type bspec0 (spec: (text -> Type)) (b:block) = 
  (exists (t:text). spec t /\ b = encode t)

type bspec1 (spec: (text -> Type)) (b:block) = 
  (exists (t:text). spec t /\ b = encode t)

opaque type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = 
  k:key{ BMAC.key_prop (fst k) == bspec0 p
      /\ BMAC.key_prop (snd k) == bspec1 p }

val keygen: p:(text -> Type) -> pkey p
val mac:    k:key -> t:text{key_prop k t} -> tag
val verify: k:key -> t:text -> tag -> b:bool{b ==> key_prop k t}

(*
let keygen spec = 
  let k0 = BMAC.keygen (bspec0 spec) in
  let k1 = BMAC.keygen (bspec1 spec) in
  let k = (k0,k1) in
  not typing:  assume (key_prop k spec);
  k
 *)

let mac (k0,k1) t = 
  if length t < blocksize 
  then BMAC.mac k0 (encode t)
  else BMAC.mac k1 t

let verify (k0,k1) t tag =   
  if length t < blocksize
  then BMAC.verify k0 (encode t) tag
  else BMAC.verify k1 (encode t) tag
