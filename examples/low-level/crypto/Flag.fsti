module Flag

(** All the idealization flags that we use for the cryptographic argument *)

val aes_prf:bool
val chacha20_prf:bool

// TODO check with Nik that this will normalize properly when all branches
// evaluate to false
let prf (i: Plain.id) =
  let open BlockCipher in
  match Block.alg_of_id i with
  | AES256 -> aes_prf
  | CHACHA20 -> chacha20_prf

// TODO jonathan horrible syntax
val poly1305_mac1:(poly1305_mac1:bool{poly1305_mac1 ==> prf})
val ghash_mac1:(ghash_mac1:bool{ghash_mac1 ==> prf})

let mac1 (i: Plain.id) =
  let open MAC in
  match MAC.alg_of_id id with
  | POLY1305 -> poly1305_mac1
  | GHASH -> ghash_mac1

val prf_enc:(prf_enc:bool{prf_enc ==> mac1})
