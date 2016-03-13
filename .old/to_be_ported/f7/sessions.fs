(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module Sessions
open Data
open Crypto
open Principals
type principal = string

let pickle b = b
let unpickle b = b
let sha1_verify x h = if sha1 x = h then () else failwith "sha1 failed"
let psend a m = ()
let precv a = failwith "not implemented"
let check_cache x y z = ()

let gen_keys session a b = 
    genMACKey session a b;
    genEncryptionKey session a b;
    let mk = getMACKey session a b in
    let ek = getEncryptionKey session a b in
    let signk = getPrivateKey session a in
    let pubk = getPublicKey session b in
    let encmsg = Crypto.rsa_encrypt pubk (concat (symkeytobytes ek) (symkeytobytes mk)) in
    concat encmsg (Crypto.rsa_sign signk encmsg)

let reg_keys session a b msg = ()
