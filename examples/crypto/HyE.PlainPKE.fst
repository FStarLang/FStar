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


(* two pure functions, never called when ideal *)
val repr: p:protected_pke_plain{not pke_ind_cca || not (honest p.i)} -> Tot pke_plain
let repr p = HyE.AE.leak_key p.k

val coerce: parent:rid -> pke_plain -> ST protected_pke_plain
  (requires (fun h0 -> True))
  (ensures (fun h0 p h1 ->
    not (honest p.i)))
let coerce parent p_plain = 
  let i = dishonestId() in
  Prot_pke_p i (HyE.AE.coerce_key i parent p_plain )
