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

noeq type protected_pke_plain =
  | Prot_pke_p : i:id -> k:AE.key i -> protected_pke_plain

type pke_plain = aes_key 

val get_index: protected_pke_plain -> Tot id
let get_index p =
  p.i

(* two pure functions, never called when ideal *)
val repr: p:protected_pke_plain{not pke_ind_cca || not (honest p.i)} -> Tot pke_plain
let repr p = HyE.AE.leak_key p.k

val coerce: #i:id{not (honest i)} -> parent:rid -> pke_plain -> St (protected_pke_plain)
let coerce #i parent p_plain = 
  Prot_pke_p i (HyE.AE.coerce_key i parent p_plain)
