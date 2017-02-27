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
module Box.Flags

val prf_odh : bool

val ae_int_ctxt : bool

val ae_ind_cpa : bool

val ae_ind_cca : b:bool

val pkae : b:bool{b <==> (ae_ind_cca /\ prf_odh)}

