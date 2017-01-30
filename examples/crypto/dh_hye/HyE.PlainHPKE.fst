(**
   TODO: Documentation and some cleaup.
*)
module HyE.PlainHPKE

open HyE.Flags
open HyE.Indexing
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open Platform.Bytes


abstract type protected_hpke_plain (i:id) = bytes 
//assume Plain_hasEq: hasEq protected_hpke_plain
type hpke_plain (i:id) = bytes

(* two pure functions, never called when ideal *)
val repr: #i:id -> p:protected_hpke_plain i{not hpke_ind_cca || not (honest i)} -> Tot (hpke_plain i)
let repr #i p = p

// Change this if we want to use signcryption with hpke_int-ctxt
val coerce: #i:id -> p:hpke_plain i{not hpke_ind_cca || not (honest i)} -> Tot (protected_hpke_plain i)
let coerce #i p = p  

val length: #i:id -> protected_hpke_plain i -> Tot nat
let length #i p = length p

// Create coece_keyshare function
