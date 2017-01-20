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
type plain_content (i:id) = (
  if honest i then
    protected_hpke_plain
  else 
    bytes
  )

abstract type protected_ae_plain =
  | Protected_ae_plain: #i:id -> p:plain_content i -> protected_ae_plain

assume Plain_hasEq: hasEq protected_ae_plain

type ae_plain = bytes

val ae_message_wrap: #i:id -> (p:plain_content i) -> protected_ae_plain
let ae_message_wrap #i p =
  Protected_ae_plain #i p

val ae_message_unwrap: protected_ae_plain -> protected_hpke_plain
let ae_message_unwrap p =
  if honest p.i then
    p.p
  else 
    PlainHPKE.coerce p.p
  
  
(**
   We allow a transition from protected_ae_plain to ae_plain only if either there is no
   idealization or if if the message is not honest.
*)
val repr: p:protected_ae_plain{not ae_ind_cca || not (honest p.i)} -> Tot ae_plain
let repr p = 
  if honest p.i then
    PlainHPKE.repr p.p
  else
    p.p

(**
   Coerced messages can only be flagged as not honest.
*)
val coerce: #i:id{not ae_int_ctxt || not (honest i)} -> p:ae_plain -> Tot protected_ae_plain
let coerce #i p = 
  if honest i then
    let coerced_p = PlainHPKE.coerce p in
    Protected_ae_plain #i coerced_p
  else
    Protected_ae_plain #i p
  
val length: protected_ae_plain -> Tot nat
let length p = 
  if honest p.i then
    PlainHPKE.length p.p
  else
    length p.p

val getIndex: protected_ae_plain -> Tot id
let getIndex p = p.i
