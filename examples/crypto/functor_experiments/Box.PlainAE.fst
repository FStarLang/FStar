module Box.PlainAE

open CoreCrypto
open Box.Flags
open Box.Indexing
open Box.PlainPKAE
open Platform.Bytes

(**
   The content of the AE payload depends on the honesty of the message.
   If it is an honest message, it encapsulates a (protected) pkae payload.
   If it is not an honest message, it is plain bytes.
*)


abstract type protected_ae_plain (i:ae_id)= p:protected_pkae_plain{get_index p = i}

type ae_plain = bytes

val length: #i:ae_id -> (protected_ae_plain i) -> Tot nat
let length #i p = PlainPKAE.length #i p

(**
   Coerced messages can only be flagged as not honest.
*)
val coerce: #i:ae_id -> p:ae_plain{not ae_ind_cca \/ (ae_dishonest i)} -> Tot (protected_ae_plain i)
let coerce #i p = 
  PlainPKAE.coerce #i p


(**
   We allow a transition from protected_ae_plain to ae_plain only if either there is no
   idealization or if if the message is not honest.
*)
val repr: #i:ae_id -> p:protected_ae_plain i{not ae_ind_cca \/ (ae_dishonest i)} -> Tot (ae_plain)
let repr #i p = 
    PlainPKAE.repr p 


(**
   This is a helper function used by PKAE.encrypt to encapsulate the payload before
   passing it on to AE.encrypt. If AE is idealized and the payload is honest, then we 
   wrap the payload into our abstract type in good faith. If not, we coerce it.
*)
val ae_message_wrap: #i:ae_id -> p:protected_pkae_plain{get_index p = i} -> Tot (protected_ae_plain i)
let ae_message_wrap #i p = p

(**
   This is the reverse function to ae_message_wrap. PKAE.decrypt uses it to extract a
   protected ae payload. If it AE is idealized and the payload is honest, then
   we strip it of its protection in good faith. Otherwise we break it down to its 
   byte representation using repr.
*)
val ae_message_unwrap: #i:ae_id -> p:protected_ae_plain i -> Tot (p:protected_pkae_plain{get_index p = i})
let ae_message_unwrap #i p = p
 
