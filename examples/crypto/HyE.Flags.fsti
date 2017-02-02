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

val pke_ind_cca : bool

val ae_int_ctxt : bool

val ae_ind_cpa : bool

val ae_ind_cca : b:bool{ae_ind_cpa /\ ae_int_ctxt ==> b}

val hpke_ind_cca : b:bool{b ==> b2t ae_ind_cca /\ pke_ind_cca}

type dependent_ae_id =
  (if pke_ind_cca then
    i:ae_id{b2t (ae_honest i)}
  else
    i:ae_id{not (ae_honest i)})

val createId: unit -> Tot dependent_ae_id

val honest_implies_pke_inc_cca: i:ae_id -> Lemma
  (requires b2t (ae_honest i))
  (ensures (pke_ind_cca))
  [SMTPat (ae_honest i)]
