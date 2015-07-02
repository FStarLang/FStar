(*--build-config
    options:--z3timeout 10 --prims ../../lib/prims.fst --verify_module SHA1 --admit_fsi Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:LIB=../../lib;
    other-files:$LIB/string.fst $LIB/list.fst
            $LIB/ext.fst $LIB/classical.fst
            $LIB/set.fsi $LIB/set.fst
            $LIB/heap.fst $LIB/st.fst
            $LIB/seq.fsi $LIB/seqproperties.fst
            Bytes.fst
  --*)
module SHA1
open Seq
open Platform.Bytes

(*type bytes = seq byte (* concrete byte arrays *)*)
type text  = bytes    (* a type abbreviation, for clarity *)

type nbytes (n:nat) =
  b:bytes{length b == n} (* fixed-length bytes *)

(* we rely on some external crypto library implementing HMAC-SHA1 *)

let keysize = 16
let blocksize = keysize
let macsize = 20

type key = nbytes keysize
type tag = nbytes macsize

val sample: n:nat -> nbytes n
let sample n = magic()

val sha1: bytes -> Tot tag
let sha1 bs = magic()

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
