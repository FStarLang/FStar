
module Patterns

let is_handshake13_signatureScheme =
  function
  | ECDSA_SECP256R1_SHA256 when a -> true
  | ECDSA_SECP256R1_SHA256 | ECDSA_SECP384R1_SHA384 when a -> true
  | ECDSA_SECP384R1_SHA384
  | ECDSA_SECP521R1_SHA512
  | RSA_PSS_SHA256
  | RSA_PSS_SHA384
  | RSA_PSS_SHA512 when a -> true
  | ECDSA_SECP256R1_SHA256
  | ECDSA_SECP384R1_SHA384
  | ECDSA_SECP521R1_SHA512
  | RSA_PSS_SHA256
  | RSA_PSS_SHA384
  | RSA_PSS_SHA512 ->
    (match l with
      | [] -> true
      | _ -> false)
  | _ -> false

