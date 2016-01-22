(*--build-config
    options:--z3timeout 10 --verify_module SHA1 --admit_fsi FStar.Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:CONTRIB=../../contrib;
    other-files:
            FStar.FunctionalExtensionality.fst FStar.Classical.fst
            FStar.Set.fsi FStar.Set.fst
            FStar.Heap.fst FStar.ST.fst FStar.All.fst
            FStar.String.fst FStar.List.fst
            seq.fsi FStar.SeqProperties.fst
            FStar.IO.fsti
            $CONTRIB/Platform/fst/Bytes.fst
            $CONTRIB/CoreCrypto/fst/CoreCrypto.fst
  --*)
module SHA1
open FStar.Seq
open Platform.Bytes
open CoreCrypto

type text  = bytes    (* a type abbreviation, for clarity *)


(* we rely on some external crypto library implementing HMAC-SHA1 *)

let keysize = 16
let blocksize = keysize
let macsize = 20

type key = lbytes keysize
type tag = bytes //lbytes macsize

val sample: n:nat -> lbytes n
let sample n = random n

let sha1 b = hash SHA1 b

val hmac_sha1: key -> text -> Tot tag
let hmac_sha1 k t =
  let x5c = byte_of_int 92 in
  let x36 = byte_of_int 54 in
  let opad = createBytes blocksize x5c in
  let ipad = createBytes blocksize x36 in
  let xor_key_opad = xor k opad (length k) in
  let xor_key_ipad = xor k ipad (length k) in
  sha1 ( xor_key_opad @|
                (sha1 (xor_key_ipad @| t))
       )
