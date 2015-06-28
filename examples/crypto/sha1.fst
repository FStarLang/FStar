module SHA1
open Array

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
