(**
   TODO: Documentation.
*)
module HyE.PlainPKE

open Platform.Bytes
open HyE.RSA
open HyE.Flags
open HyE.AE
open HyE.Indexing
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef

type protected_pke_plain (i:pke_id) = k:AE.key{i= fst (get_index k)}

type pke_plain (i:pke_id) = aes_key 

(* two pure functions, never called when ideal *)
val repr: #i:pke_id -> p:protected_pke_plain i{not pke_ind_cca || not (pke_honest i)} -> Tot (pke_plain i)
let repr #i p = HyE.AE.leak_key #(AE.get_index p) p

// Not sure how the ids are supposed to work with coerce...
val coerce: #i:ae_id{not (ae_honest i) || not ae_ind_cca} -> parent:rid -> pke_plain (fst i) -> St (p:protected_pke_plain (fst i))
let coerce #i parent p_plain = 
  HyE.AE.coerce_key i parent p_plain
