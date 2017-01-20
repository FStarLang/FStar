(**
   This module contains flags that control the idealization of encryption and decryption,
   both of AE and of PKE. The flags indicate whether certain assumption are assumed to be
   true or not. Also, the refinements on the flag type indicate implications between the
   assumptions such as ae_ind_cpa /\ ae_int_ctxt ==> ae_ind_cca.
   Not that for purposes of type-checking, the flags are not set. This
   ensures that the program is well typed for any permutation of set flags (that is permissible
   by the refinements).
*)
module HyE.Flags

open HyE.Indexing

//val pke_ind_cca : bool
let pke_ind_cca = false

val ae_int_ctxt : bool
//let ae_int_ctxt = false

val ae_ind_cpa : bool

val ae_ind_cca : b:bool{ae_ind_cpa /\ ae_int_ctxt ==> b}
//let ae_ind_cca = true

val hpke_ind_cca : b:bool{b ==> b2t ae_ind_cca /\ pke_ind_cca}
//let hpke_ind_cca = true

val honest: i:id -> Tot bool

val dishonestId: unit -> Tot (i:id{not (honest i)})
val honestId: unit -> Tot (i:id{honest i})

type dependentId =
  (if pke_ind_cca then
    i:id{honest i}
  else
    i:id{not (honest i)})

val createId: unit -> Tot dependentId
//val createId: unit -> Tot (i:id{pke_ind_cca ==> honest i})
//val createId: unit -> Tot (i:id{honest i})

(* Do we really need these? Better encode them in the types.*)
//val ae_ind_cca_composition_lemma: unit -> Lemma
//  (requires ae_ind_cpa /\ ae_int_ctxt)
//  (ensures b2t ae_ind_cca)
//
//val ind_cca_composition_lemma: unit -> Lemma
//  (requires b2t ae_ind_cca /\ pke_ind_cca)
//  (ensures b2t hpke_ind_cca)
//
//val hpke_cca_implications_lemma: unit -> Lemma
//  (requires b2t hpke_ind_cca)
//  (ensures b2t ae_ind_cca /\ pke_ind_cca)

val honest_implies_pke_inc_cca: i:id -> Lemma
  (requires honest i)
  (ensures (pke_ind_cca))
  [SMTPat (honest i)]
