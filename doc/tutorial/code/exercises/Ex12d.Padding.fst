module Pad
open Array

(* a coercion; avoid it? *)
assume val n2b: n:nat {( n < 256 )} -> Tot uint8
assume val b2n: b:uint8 -> Tot (n:nat { (n < 256) /\ n2b n = b })

type bytes = seq byte (* concrete byte arrays *) 
type nbytes (n:nat) = b:bytes{length b == n} (* fixed-length bytes *)

let blocksize = 32 
type block = nbytes blocksize
type text = b:bytes {(length b < blocksize)}

(* fill in type here *)
let pad n = 
  Array.create n (n2b (n-1))  

(* pad 1 = [| 0 |]; pad 2 = [| 1; 1 |]; ... *)

(* fill in type here *)
let encode a = append a (pad (blocksize - length a))

(* fill in type here *)
let decode (b:block) = 
  let padsize = b2n(index b (blocksize - 1)) + 1 in
  if op_LessThan padsize blocksize then 
    let (plain,padding) = split b (blocksize - padsize) in
    if padding = pad padsize
    then Some plain
    else None   
  else None


