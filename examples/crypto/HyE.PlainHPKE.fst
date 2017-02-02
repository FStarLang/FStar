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

type hpke_plain = Bytes.bytes

abstract type protected_hpke_plain (i:pke_id)= 
  | Prot_hpke_p: b:hpke_plain -> protected_hpke_plain i

(* two pure functions, never called when ideal *)
val repr: #i:pke_id -> p:protected_hpke_plain i{not (pke_honest i) || not hpke_ind_cca} -> Tot (hpke_plain)
let repr #i p = p.b

// Change this if we want to use signcryption with hpke_int-ctxt
val coerce: #i:pke_id -> p:hpke_plain{not (pke_honest i) || not hpke_ind_cca} -> Tot (protected_hpke_plain i)
let coerce #i p = 
  Prot_hpke_p #i p

val length: #i:pke_id -> protected_hpke_plain i -> Tot nat
let length #i p = Bytes.length p.b
