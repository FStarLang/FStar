module Padding.Pad

open FStar.Seq
open FStar.SeqProperties
open FStar.BaseTypes
open Platform.Bytes

(* a coercion; avoid it? *)
assume val n2b: n:nat {( n < 256 )} -> Tot (b:byte{b==n})
assume val b2n: b:byte -> Tot (n:nat { (n < 256) /\ b == n})

type bytes = seq byte (* concrete byte arrays *)
type nbytes (n:nat) = b:bytes{length b == n} (* fixed-length bytes *)

let blocksize = 32
type block = nbytes blocksize
type text = b:bytes {(length b < blocksize)}

val pad: n:nat { 1 <= n /\ n <= blocksize } -> Tot (nbytes n)
let pad n = createBytes n (n2b (n-1))

(* pad 1 = [| 0 |]; pad 2 = [| 1; 1 |]; ... *)


val encode: a: text -> Tot block
let encode a = append a (pad (blocksize - length a))

val inj: a: text -> b: text -> Lemma (requires (Seq.Eq (encode a) (encode b)))
                                     (ensures (Seq.Eq a b))
                                     [SMTPat (encode a); SMTPat (encode b)]
                                     (decreases (length a))
let inj a b =
  if length a = length b
  then
    begin
    lemma_append_inj a (pad (blocksize - length a)) b (pad (blocksize - length b));
    ()
    end
  else let aa = encode a in
       let bb = encode b in
       cut (Seq.index aa 31 =!= Seq.index bb 31)


val decode: b:block -> Tot (option (t:text { Seq.Eq b (encode t) }))
let decode (b:block) =
  let padsize = b2n(index b (blocksize - 1)) + 1 in
  if (padsize < blocksize)
  then
    let (plain,padding) = split b (blocksize - padsize) in
    if padding=pad padsize
    then let tt = encode plain in
         Some plain
    else None
  else None
