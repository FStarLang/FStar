module Ex12e.Pad

open FStar.UInt8
open FStar.Seq


type uint8 = FStar.UInt8.t

(* a coercion; avoid it? *)
assume val n2b: n:nat {( n < 256 )} -> Tot uint8
assume val b2n: b:uint8 -> Tot (n:nat { (n < 256) /\ n2b n = b })

type bytes = seq byte (* concrete byte arrays *) 
type nbytes (n:nat) = b:bytes{length b == n} (* fixed-length bytes *)

let blocksize = 32 
type block = nbytes blocksize
type text = b:bytes {(length b < blocksize)}

val pad: n:nat { 1 <= n /\ n <= blocksize } -> Tot (nbytes n)

let pad n = 
  Seq.create n (n2b (n-1))  

(* pad 1 = [| 0 |]; pad 2 = [| 1; 1 |]; ... *)

val encode: a: text -> Tot block 
let encode a = append a (pad (blocksize - length a))

val inj: a: text -> b: text -> Lemma (requires (True (*complete lemma here*)))
                                     (ensures (True (*and here*)))
				     [SMTPat (encode a); SMTPat (encode b)]
let inj a b = ()


val decode: b:block -> option (t:text { equal b (encode t) })
let decode (b:block) = 
  let padsize = b2n(index b (blocksize - 1)) + 1 in
  if op_LessThan padsize blocksize then 
    let (plain,padding) = split b (blocksize - padsize) in
    if  Seq.eq padding (pad padsize)
    then Some plain
    else None   
  else None
