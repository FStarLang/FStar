module Box.PlainAE

open CoreCrypto
open Box.Flags
open Box.Indexing
open Box.PlainPKAE
open Platform.Bytes


abstract type protected_ae_plain (i:id{AE_id? i}) = p:protected_pkae_plain{get_index p = i}

type ae_plain = bytes

val length: #i:id{AE_id? i} -> (protected_ae_plain i) -> Tot nat
let length #i p = PlainPKAE.length p

(**
   Coerced messages can only be flagged as not honest.
*)
val coerce: #i:id{AE_id? i} -> p:ae_plain{not ae_ind_cca \/ (dishonest i)} -> Tot (protected_ae_plain i)
let coerce #i p = 
  PlainPKAE.coerce #i p


(**
   We allow a transition from protected_ae_plain to ae_plain only if either there is no
   idealization or if if the message is not honest.
*)
val repr: #i:id{AE_id? i} -> p:protected_ae_plain i{not ae_ind_cca \/ (dishonest i)} -> Tot (ae_plain)
let repr #i p = 
    PlainPKAE.repr p 


(**
   This is a helper function used by PKAE.encrypt to encapsulate the payload before
   passing it on to AE.encrypt. If AE is idealized and the payload is honest, then we 
   wrap the payload into our abstract type in good faith. If not, we coerce it.
*)
val ae_message_wrap: #i:id{AE_id? i} -> p:protected_pkae_plain{get_index p = i} -> Tot (protected_ae_plain i)
let ae_message_wrap #i p = p

(**
   This is the reverse function to ae_message_wrap. PKAE.decrypt uses it to extract a
   protected ae payload. If it AE is idealized and the payload is honest, then
   we strip it of its protection in good faith. Otherwise we break it down to its 
   byte representation using repr.
*)
val ae_message_unwrap: #i:id{AE_id? i} -> p:protected_ae_plain i -> Tot (p:protected_pkae_plain{get_index p = i})
let ae_message_unwrap #i p = p
 
