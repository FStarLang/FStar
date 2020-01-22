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
module OPLSS.HMACSHA1
open OPLSS

let keysize   = 64
let blocksize = keysize
let macsize   = 20

assume //demo scaffolding
val sha1: bytes -> Tot (h:bytes{Seq.length h = macsize})

let msg = bytes
type sha1_key = lbytes keysize
type tag = lbytes macsize

let hmac_sha1 (k:sha1_key) (m:msg)
  : tag =
  let x5c = byte_of_int 92 in
  let x36 = byte_of_int 54 in
  let opad = Seq.create blocksize x5c in
  let ipad = Seq.create blocksize x36 in
  let xor_key_opad = xor keysize k opad in
  let xor_key_ipad = xor keysize k ipad in
  sha1 (xor_key_opad `Seq.append`
       (sha1 (xor_key_ipad `Seq.append` m)))

