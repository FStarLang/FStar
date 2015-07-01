(*--build-config
    options:--z3timeout 10 --prims ../../lib/prims.fst --verify_module SHA1 --admit_fsi Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:LIB=../../lib;
    other-files:$LIB/string.fst $LIB/list.fst
            $LIB/ext.fst $LIB/classical.fst
            $LIB/set.fsi $LIB/set.fst
            $LIB/heap.fst $LIB/st.fst
            $LIB/seq.fsi $LIB/seqproperties.fst
  --*)
module SHA1
open Seq

type bytes = seq byte (* concrete byte arrays *)
type text  = bytes    (* a type abbreviation, for clarity *)

type nbytes (n:nat) =
  b:bytes{length b == n} (* fixed-length bytes *)

(* we rely on some external crypto library implementing HMAC-SHA1 *)

let keysize = 16
let macsize = 20

type key = nbytes keysize
type tag = nbytes macsize

val sample: n:nat -> nbytes n
let sample n = magic()
val sha1: key -> text -> Tot tag
let sha1 k t = magic()

(* to verify, we simply recompute & compare *)

val sha1verify: key -> text -> tag -> Tot bool
let sha1verify k txt tag = (sha1 k txt = tag)
