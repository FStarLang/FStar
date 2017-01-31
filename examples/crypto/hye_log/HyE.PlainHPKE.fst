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

abstract type protected_hpke_plain = 
  | Prot_hpke_p: #i:id -> b:bytes -> protected_hpke_plain
//assume Plain_hasEq: hasEq protected_hpke_plain
type hpke_plain = bytes

val get_index: protected_hpke_plain -> Tot id
let get_index p =
  p.i

(* two pure functions, never called when ideal *)
val repr: p:protected_hpke_plain{not (honest p.i) || not hpke_ind_cca} -> Tot (hpke_plain)
let repr p = p.b

// Change this if we want to use signcryption with hpke_int-ctxt
val coerce: #i:id -> p:hpke_plain{not (honest i) || not hpke_ind_cca} -> Tot (protected_hpke_plain)
let coerce #i p = 
  Prot_hpke_p #i p

val length: protected_hpke_plain -> Tot nat
let length p = length p.b
