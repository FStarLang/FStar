module HyE.PlainAE

open CoreCrypto
open HyE.Flags
open HyE.Indexing
open HyE.PlainHPKE
open Platform.Bytes

(**
   The content of the AE payload depends on the honesty of the message.
   If it is an honest message, it encapsulates a (protected) hpke payload.
   If it is not an hones message, it is plain bytes.
*)
type ae_plain_content (i:id) = (
  if honest i then
    protected_hpke_plain
  else 
    bytes
  )

abstract type protected_ae_plain (i:id)=
  | Protected_ae_plain: (p:ae_plain_content i) -> protected_ae_plain i

type ae_plain = bytes

(**
   TODO: Review these functions and add pre-conditions?
*)
val ae_message_wrap: #i:id -> (p:ae_plain_content i) -> Tot (protected_ae_plain i)
let ae_message_wrap #i p =
  Protected_ae_plain p

val ae_message_unwrap: #i:id -> protected_ae_plain i -> Tot protected_hpke_plain
let ae_message_unwrap #i p =
  if honest i then
    p.p
  else 
    PlainHPKE.coerce p.p
  
(**
   We allow a transition from protected_ae_plain to ae_plain only if either there is no
   idealization or if if the message is not honest.
*)
val repr: #i:id -> p:protected_ae_plain i{not ae_ind_cca || not (honest i)} -> Tot ae_plain
let repr #i p = 
  if honest i then
    PlainHPKE.repr p.p 
  else
    p.p

(**
   Coerced messages can only be flagged as not honest.
*)
val coerce: #i:id -> p:ae_plain{not ae_int_ctxt || not (honest i)} -> Tot (protected_ae_plain i)
let coerce #i p = 
  if honest i then
    let coerced_p = PlainHPKE.coerce p in
    Protected_ae_plain #i coerced_p
  else
    Protected_ae_plain #i p
  
val length: #i:id -> (protected_ae_plain i) -> Tot nat
let length #i p = 
  if honest i then
    PlainHPKE.length p.p
  else
    length p.p
