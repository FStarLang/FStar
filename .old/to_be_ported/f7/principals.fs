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
module Principals
(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)
(********************************************************)
(* The Database of Principals *)
(*********************************************************
   Defines:
     type principalU: username-password
     type principalX: X.509 certificates
 *********************************************************)

open Pi
open F7
open Data
open Crypto
open Db

type a = (str, str) t
type prin = str
type usage = bytes

type preds = 
  | PublicKeyPair of (usage * prin * key * key)
  | SharedKeyPair of (usage * prin * prin * key * key)
  | Password of (usage * prin * prin * str)
  | EncryptionKey of (usage * prin * prin * key)
  | MACKey of (usage * prin * prin * key)
  | Bad of prin
  | PrivateKey of (usage * prin * key)
  | PublicKey of (usage * prin * key)
  | SendFrom of (usage * prin * bytes)
  | EncryptTo of (usage * prin * bytes)
  | Send of (usage * prin * prin * bytes)
  | Encrypt of (usage * prin * prin * bytes)
  | SecretNonce of (prin * prin * bytes)
let mkPublicKeyPair u a =
  let sk = rsa_keygen () in // freshness proving (PublicKeyPair Injective)
  let pk = rsa_pub sk in
#if f7
  // proves (PublicKeyPair PubPrivKeyPair)
  expect (Crypto.PubPrivKeyPair(pk,sk)); 
#endif
  Assume (PublicKeyPair(u,a,pk,sk));
  (pk,sk)

let mkSharedKeyPair u a b =
  let sk = aes_keygen () in
  let mk = hmac_keygen () in
  Assume (SharedKeyPair(u,a,b,sk,mk));
  (sk,mk)

let mkEncryptionKey u a b =
  let ek = aes_keygen () in
  Assume (EncryptionKey(u,a,b,ek));
  ek

let mkMACKey u a b =
  let mk = hmac_keygen () in
  Assume (MACKey(u,a,b,mk));
  mk

let hmacsha1 u a b mk m = Crypto.hmacsha1 mk m
let hmacsha1Verify u a b mk m h = Crypto.hmacsha1Verify mk m h

let aes_encrypt u a b k m = Crypto.aes_encrypt k m
let aes_decrypt u a b k m = Crypto.aes_decrypt k m
let aes_decrypt_pub u a b k m = Crypto.aes_decrypt k m


let rsa_encrypt u a k m = Crypto.rsa_encrypt k m
let rsa_decrypt u a k m = Crypto.rsa_decrypt k m

let rsa_encrypt_oaep u a k m = Crypto.rsa_encrypt_oaep k m
let rsa_decrypt_oaep u a k m = Crypto.rsa_decrypt_oaep k m

let rsa_sign u a k m = Crypto.rsa_sign k m
let rsa_verify u a k m s = Crypto.rsa_verify k m s

#if pvlimited

let fst (x,y) = x
let snd (x,y) = y
let usage = mkNonce()
let prina = str "A"
let ka =  mkPublicKeyPair usage prina
let pka = fst ka
let ska = snd ka

let prinb = str "B"
let kb =  mkPublicKeyPair usage prinb
let pkb = fst kb
let skb = snd kb

let prins = str "S"
let ks =  mkPublicKeyPair usage prins
let pks = fst ks
let sks = snd ks

let genPublicKeyPair u x = ()
let genSharedKeyPair u x = ()
let genEncryptionKey u x = ()
let genMACKey u x = ()

let getPublicKeyPair u x = 
  let pa = str "a" in
  let pb = str "b" in
  let ps = str "s" in
  match x with
      _ when x = pa -> (pka,ska)
    | _ when x = pb -> (pkb,skb)
    | _ when x = ps -> (pks,sks)
    | _ ->  failwith "unknown user"

let getPrivateKey u x = snd (getPublicKeyPair u x)
let getPublicKey u x = fst (getPublicKeyPair u x)

let sk = genEncryptionKey usage prina prinb
let mk = genMACKey usage prina prinb
let genPassword u a b = ()
let getPassword u a b = str "password"
let leakPassword u a b = assume(Bad(a));str "password"
let getSharedKeyPair u a b = (sk,mk)
let getEncryptionKey u a b = sk
let getMACKey u a b = mk

#else

let pkeydb = (* (usage * prin, (u:usage * a:prin * pk:key * sk:key)) Db_t *)
  Db.create ()

let skeydb = (* ((usage * prin * prin), (usage * prin * prin * key * key)) Db_t = *)
  Db.create ()

let ekeydb = (*  ((usage * prin * prin), (usage * prin * prin * key)) Db_t = *)
  Db.create ()

let mkeydb = (* ((usage * prin * prin), (usage * prin * prin * key)) Db_t = *)
  Db.create ()

let genPublicKeyPair u a = 
  let (pk,sk) = mkPublicKeyPair u a in
  Db.insert pkeydb (u,a) (u,a,pk,sk)

let genSharedKeyPair u a b = 
  let (sk,mk) = mkSharedKeyPair u a b in
  Db.insert skeydb (u,a,b) (u,a,b,sk,mk)

let genEncryptionKey u a b = 
  let sk = mkEncryptionKey u a b in
  Db.insert ekeydb (u,a,b) (u,a,b,sk)

let genMACKey u a b = 
  let mk = mkMACKey u a b in
  Db.insert mkeydb (u,a,b) (u,a,b,mk)

let getPublicKeyPair u a = 
  let (uu,aa,pk,sk) = Db.select pkeydb (u,a) in
  if (u,a) = (uu,aa) then (pk,sk)
  else failwith "Db.select returned wrong element"

let getPrivateKey u a = 
  let (uu,aa,pk,sk) = Db.select pkeydb (u,a) in
  if (u,a) = (uu,aa) then sk 
  else failwith "Db.select returned wrong element"

let getPublicKey u a = 
  let (uu,aa,pk,sk) = Db.select pkeydb (u,a) in
  if (u,a) = (uu,aa) then pk
  else failwith "Db.select returned wrong element"

let getSharedKeyPair u a b = 
  let (uu,aa,bb,sk,mk) = Db.select skeydb (u,a,b) in
  if (u,a,b) = (uu,aa,bb) then (sk,mk)
  else failwith "Db.select returned wrong element"

let getEncryptionKey u a b = 
  let (uu,aa,bb,ek) = Db.select ekeydb (u,a,b) in
  if (u,a,b) = (uu,aa,bb) then ek 
  else failwith "Db.select returned wrong element"

let getMACKey u a b = 
  let (uu,aa,bb,mk) = Db.select mkeydb (u,a,b) in
  if (u,a,b) = (uu,aa,bb) then mk 
  else failwith "Db.select returned wrong element"

// Two-party secrets


let mkSecretNonce a b = 
  let n = mkNonce() in
   Assume (SecretNonce(a,b,n));
   n

let pwddb = (* : ((usage * prin * prin), (usage * prin * prin * str)) Db_t =*)
  Db.create ()

let mkPassword u c s = 
  let n = mkNonce () in
  let p = base64 n in
  Assume (Password(u,c,s,p));
  p

let genPassword u c s = 
  let p = mkPassword u c s in
  Db.insert pwddb (u,c,s) (u,c,s,p)

let getPassword u c s = 
  let (uu,cc,ss,p) = Db.select pwddb (u,c,s) in
  if (uu,cc,ss) = (u,c,s) then p
  else failwith "Db.select returned wrong element"

let leakPassword u a s = 
  let p = getPassword u a s in
  Assume (Bad(a));
  p
#endif

let leakPrivateKey u a = 
  let sk = getPrivateKey u a in
  Assume (Bad(a));
  rsa_keycomp sk;
  sk

let leakEncryptionKey u a b = 
  let sk = getEncryptionKey u a b in
  Assume (Bad(a));
  Assume (Bad(b));
  aes_keycomp sk;
  sk

let leakMACKey u a b = 
  let mk = getMACKey u a b in
  Assume (Bad(a));
  Assume (Bad(b));
  hmac_keycomp mk;
  mk

