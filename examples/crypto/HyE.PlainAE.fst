module HyE.PlainAE

open CoreCrypto
open HyE.Flags
open HyE.Indexing
open HyE.PlainHPKE
open Platform.Bytes

module B = Platform.Bytes

(**
   If we give guarantees for hpke and the plaintext is pke_honest, 
   but not ae_honest, then we do not protect it on hpke_level. On
   the other hand, if we do not give guarantees on the pke level or
   the plaintext is not pke_honest, we can "protect" it and call repr.
   This allows us to avoid branching on the pke_honesty of the plaintext
   in HPKE.encrypt.
*)
type protected_ae_plain (i:ae_id) = (
  if (pke_honest (fst i) && hpke_ind_cca) && not (ae_honest i && ae_ind_cca) then
    hpke_plain
  else 
    protected_hpke_plain (fst i)
  )

type ae_plain = B.bytes

val length: #i:ae_id -> (protected_ae_plain i) -> Tot nat
let length #i p = 
  if (pke_honest (fst i) && hpke_ind_cca) && not (ae_honest i && ae_ind_cca) then
    B.length p
  else
    PlainHPKE.length #(fst i) p


(**
   Coerced messages can only be flagged as not honest. The if condition reflects the
   dependent nature of the protected_ae_plain type. If we have protection on the
   HPKE level, we have to call coerce.
*)
val coerce: #i:ae_id -> p:ae_plain{not ae_ind_cca || not (ae_honest i)} -> Tot (protected_ae_plain i)
let coerce #i p = 
  if (pke_honest (fst i) && hpke_ind_cca) && not (ae_honest i && ae_ind_cca) then
    p
  else 
    PlainHPKE.coerce #(fst i) p

(**
   We allow a transition from protected_ae_plain to ae_plain only if either there is no
   idealization or if if the message is not honest.
*)
val repr: #i:ae_id -> p:protected_ae_plain i{not ae_ind_cca || not (ae_honest i)} -> Tot (ae_plain)
let repr #i p = 
  if (pke_honest (fst i) && hpke_ind_cca) && not (ae_honest i && ae_ind_cca) then
    p
  else 
    PlainHPKE.repr #(fst i) p

val ae_unwrap: #i:ae_id -> protected_ae_plain i -> Tot (protected_hpke_plain (fst i))
let ae_unwrap #i p =
  if (pke_honest (fst i) && hpke_ind_cca) && not (ae_honest i && ae_ind_cca) then
    PlainHPKE.coerce #(fst i) p
  else 
    p
  
