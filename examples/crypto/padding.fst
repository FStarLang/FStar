(*--build-config
    options:--z3timeout 10 --verify_module Pad --admit_fsi FStar.Seq --admit_fsi FStar.Set --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    other-files: FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
            FStar.String.fst FStar.List.fst
            FStar.FunctionalExtensionality.fst FStar.Classical.fst
            seq.fsi FStar.SeqProperties.fst
  --*)

module Pad

open FStar.Seq
open FStar.SeqProperties

(* a coercion; avoid it? *)
assume val n2b: n:nat {( n < 256 )} -> Tot (b:uint8{b==n})
assume val b2n: b:uint8 -> Tot (n:nat { (n < 256) /\ b == n})

type bytes = seq byte (* concrete byte arrays *)
type nbytes (n:nat) = b:bytes{length b == n} (* fixed-length bytes *)

let blocksize = 32
type block = nbytes blocksize
type text = b:bytes {(length b < blocksize)}

val pad: n:nat { 1 <= n /\ n <= blocksize } -> Tot (nbytes n)
let pad n = Seq.create #uint8 n (n2b (n-1))

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


module MAC2

open FStar.Seq
open FStar.SeqProperties
open Pad

type text2 = b:bytes { length b <=  blocksize }

let keysize = 2 * BMAC.keysize
let macsize = BMAC.macsize
type key = | Keys: k0:BMAC.key -> k1:BMAC.key -> key
type tag = BMAC.tag

opaque type bspec0 (spec: (text2 -> Type)) (b:block) =
  (forall (t:text). b = encode t ==> spec t)

opaque type bspec1 (spec: (text2 -> Type)) (b:block) =
  spec b

opaque type key_prop : key -> text2 -> Type

type pkey (p:(text2 -> Type)) =
  k:key{ key_prop k == p
      /\ BMAC.key_prop (Keys.k0 k) == bspec0 p
      /\ BMAC.key_prop (Keys.k1 k) == bspec1 p }

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


let mac (Keys k0 k1) t =
  if length t < blocksize
  then BMAC.mac k0 (encode t)
  else BMAC.mac k1 t

let verify (Keys k0 k1) t tag =
  if length t < blocksize
  then BMAC.verify k0 (encode t) tag
  else BMAC.verify k1 t tag
