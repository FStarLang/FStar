module HyE.PlainAE

open CoreCrypto
open HyE.Flags
open HyE.Indexing
open HyE.PlainHPKE
open Platform.Bytes

(**
   The content of the AE payload depends on the honesty of the message.
   If it is an honest message, it encapsulates a (protected) hpke payload.
   If it is not an honest message, it is plain bytes.
*)

type ae_plain_content (i:ae_id) = (
  if ae_honest i && hpke_ind_cca then
    p:protected_hpke_plain{get_index p = i}
  else 
    hpke_plain
  )

noeq abstract type protected_ae_plain (i:ae_id)=
  | Protected_ae_plain: (p:ae_plain_content i) -> protected_ae_plain i

type ae_plain = bytes

val extract_id: #i:ae_id -> ae_plain_content i -> Tot (i:ae_id)
let extract_id #i p =
  i

val length: #i:ae_id -> (protected_ae_plain i) -> Tot nat
let length #i p = 
  if ae_honest i && hpke_ind_cca then
    let pk_i = fst i in
    PlainHPKE.length #i p.p
  else
    length p.p

(**
   Coerced messages can only be flagged as not honest.
*)
val coerce: #i:ae_id -> p:ae_plain_content i{not ae_ind_cca || not (ae_honest i)} -> Tot (protected_ae_plain i)
let coerce #i p = 
  Protected_ae_plain #i p

(**
   We allow a transition from protected_ae_plain to ae_plain only if either there is no
   idealization or if if the message is not honest.
*)
val repr: #i:ae_id -> p:protected_ae_plain i{not ae_ind_cca || not (ae_honest i)} -> Tot (ae_plain_content i)
let repr #i p = 
  if ae_honest i && ae_ind_cca then
    PlainHPKE.repr p.p 
  else
    p.p

(**
   This is a helper function used by HPKE.encrypt to encapsulate the payload before
   passing it on to AE.encrypt. If AE is idealized and the payload is honest, then we 
   wrap the payload into our abstract type in good faith. If not, we coerce it.
*)
val ae_message_wrap: #i:ae_id -> p:ae_plain_content i -> Tot (protected_ae_plain i)
let ae_message_wrap #i p =
  if ae_honest i && ae_ind_cca then
    Protected_ae_plain p
  else
    coerce p

(**
   This is the reverse function to ae_message_wrap. HPKE.decrypt uses it to extract a
   protected ae payload. If it AE is idealized and the payload is honest, then
   we strip it of its protection in good faith. Otherwise we break it down to its 
   byte representation using repr.
*)
val ae_message_unwrap: #i:ae_id -> p:protected_ae_plain i -> Tot (ae_plain_content i)
let ae_message_unwrap #i p =
  if ae_honest i && ae_ind_cca then
    p.p
  else 
    repr p
  
