(**
   This module contains flags that control the idealization of encryption and decryption,
   both of AE and of PKE. The flags indicate whether certain assumption are assumed to be
   true or not. Also, the refinements on the flag type indicate implications between the
   assumptions such as ae_ind_cpa /\ ae_int_ctxt ==> ae_ind_cca.
   Note, that for purposes of type-checking, the flags are not set. This
   ensures that the program is well typed for any permutation of set flags (that is permissible
   by the refinements).
   TODO: Restrict access to functions for creation of ids?
*)
module HyE.Flags

open HyE.Indexing

val prf_odh : bool

val ae_int_ctxt : bool

val ae_ind_cpa : bool

val ae_ind_cca : b:bool{ae_ind_cpa /\ ae_int_ctxt ==> b}

val hpke_ind_cca : b:bool{b ==> b2t ae_ind_cca /\ prf_odh}

val dishonestId: unit -> Tot (i:id{not (honest i)})
val honestId: unit -> Tot (i:id{honest i})

//type dependentId =
//  (if prf_odh then
//    i:id{honest i}
//  else
//    i:id{not (honest i)})
//
//val createId: unit -> Tot dependentId

val honest_implies_prf_odh: i:id -> Lemma
  (requires honest i)
  (ensures (prf_odh))
  [SMTPat (honest i)]
