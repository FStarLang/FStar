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


abstract type protected_hpke_plain = 
  | Prot_hpke_p: #i:ae_id -> b:bytes -> protected_hpke_plain
//assume Plain_hasEq: hasEq protected_hpke_plain
type hpke_plain = bytes

val get_index: p:protected_hpke_plain -> Tot (i:ae_id{i=p.i})
let get_index p =
  p.i

(* two pure functions, never called when ideal *)
val repr: p:protected_hpke_plain{not hpke_ind_cca || not (ae_honest p.i)} -> Tot hpke_plain
let repr p = p.b

// Change this if we want to use signcryption with hpke_int-ctxt
val coerce: #i:ae_id -> p:hpke_plain{not hpke_ind_cca || not (ae_honest i)} -> Tot (prot:protected_hpke_plain{i=prot.i})
let coerce #i p = 
  Prot_hpke_p #i p  

val length: #i:ae_id -> protected_hpke_plain -> Tot nat
let length #i p = length p.b

// Create coece_keyshare function
