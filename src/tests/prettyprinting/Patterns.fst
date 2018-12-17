(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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

let f =
  function
  | A when
    (v <> 0x0401 /\ v <> 0x0501 /\ v <> 0x0601 /\ v <> 0x0403 /\ v <> 0x0503 /\ v <> 0x0603 /\
      v <> 0x0804 /\ v <> 0x0805 /\ v <> 0x0806 /\ v <> 0x0201 /\ v <> 0x0203 /\ v <> 0x0202 /\
      v <> 0x0402 /\ v <> 0x0502 /\ v <> 0x0602 /\ v <> 0xFFFF) ->
    true
  | B -> true
  | C -> false

