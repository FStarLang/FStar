module Flag

open Crypto.Symmetric

(** All the idealization flags that we use for the cryptographic argument *)

val aes_prf:bool
val chacha20_prf:bool

// TODO check with Nik that this will normalize properly when all branches
// evaluate to false
let prf (i: Plain.id) =
  match BlockCipher.alg_of_id i with
  | BlockCipher.AES256 -> aes_prf
  | BlockCipher.CHACHA20 -> chacha20_prf

val poly1305_mac1: bool
val ghash_mac1: bool

val mac_log: bool

let mac1 (i: Plain.id) =
  let open Plain in
  match mac_alg_of_id i with
  | POLY1305 -> poly1305_mac1 && mac_log
  | GHASH -> ghash_mac1 && mac_log

val mac1_implies_mac_log: i:Plain.id -> Lemma
  (requires True)
  (ensures (mac1 i ==> mac_log))
  [SMTPat (mac1 i)]

val mac1_implies_prf: i:Plain.id -> Lemma
  (requires True)
  (ensures (mac1 i ==> prf i))
  [SMTPat (mac1 i)]

val prf_enc: i:Plain.id -> Tot bool

val prf_enc_implies_mac1: i:Plain.id -> Lemma
  (requires True)
  (ensures (prf_enc i ==> mac1 i))
  [SMTPat (prf_enc i)]
