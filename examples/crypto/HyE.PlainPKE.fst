(**
   TODO: Documentation.
*)
module HyE.PlainPKE

open Platform.Bytes
open HyE.RSA
open HyE.Flags
open HyE.AE
open HyE.PlainAE
open HyE.Indexing
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef

noeq type protected_pke_plain (i:pke_id) =
  | Prot_pke_plain : k:AE.key{fst (get_index k) = i} -> protected_pke_plain i

type pke_plain (i:pke_id) = aes_key 

(* two pure functions, never called when ideal *)
val repr: #i:pke_id -> p:protected_pke_plain i{not pke_ind_cca || not (pke_honest i)} -> Tot (pke_plain i)
let repr #i p = HyE.AE.leak_key #(AE.get_index p.k) p.k

// Not sure how the ids are supposed to work with coerce...
val coerce: #num:UInt32.t -> #i:pke_id{not (ae_honest (i,num))} -> parent:rid -> pke_plain i -> St (protected_pke_plain i)
let coerce #num #i parent p_plain = 
  Prot_pke_plain (HyE.AE.coerce_key (i,num) parent p_plain)
