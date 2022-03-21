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
module OPLSS.AES
open OPLSS
  
/// iv: initialization vectors
assume val ivsize : nat //demo scaffolding
let iv = lbytes ivsize

/// Raw keys for AES 128
assume val keysize : nat //demo scaffolding
let key = lbytes keysize

/// Plain text
assume val plainsize : nat //demo scaffolding
let plain = lbytes keysize


/// Cipher-texts are a concatenation of the IV and the AES cipher
///    -- we underspecify its length
///    -- MK says: minimal cipher length twice blocksize?
assume val cipher_size : nat //demo scaffolding
let cipher = lbytes cipher_size

let iv_cipher = lbytes (ivsize + cipher_size)
  
assume  //demo scaffolding
val aes_encrypt (k:key) (iv:iv) (p:plain)
  : Tot cipher
       
assume  //demo scaffolding
val aes_decrypt (k:key) (iv:iv) (c:cipher)
  : Tot plain

assume //demo scaffolding
val enc_dec_inverses (key:key) (iv:iv) (plain:plain)
    : Lemma 
      (ensures (aes_decrypt key iv (aes_encrypt key iv plain) == plain))
      [SMTPat (aes_decrypt key iv (aes_encrypt key iv plain))]       
