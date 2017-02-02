(**
   TODO: Documentation and some cleaup.
*)
module HyE.PlainHPKE

open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open Platform.Bytes

open HyE.Flags
open HyE.Indexing

module B = Platform.Bytes

type hpke_plain = B.bytes

abstract type protected_hpke_plain (i:pke_id) = hpke_plain

(* two pure functions, never called when ideal *)
val repr: #i:pke_id -> p:protected_hpke_plain i{not (pke_honest i) || not hpke_ind_cca} -> Tot (hpke_plain)
let repr #i p = p

// Change this if we want to use signcryption with hpke_int-ctxt
val coerce: #i:pke_id -> p:hpke_plain -> Tot (protected_hpke_plain i)
let coerce #i p =
  p

val length: #i:pke_id -> protected_hpke_plain i -> Tot nat
let length #i p = B.length p
