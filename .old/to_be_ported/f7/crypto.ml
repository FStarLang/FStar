(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)
module Crypto
#if pv
#else
#light "off"
#endif
open Data
open Pi
open F7
#if seals
open List
open PrimCrypto 
#endif

type key = 
  | SymKey of bytes 
  | AsymPrivKey of bytes
  | AsymPubKey of bytes
#if seals
  | SealKey of (bytes,bytes) Table 
#endif

type keypred = 
  | Pub_k of key

type usage =
  | KeySeedName 
  | MKeyName
  | SKeyName
  | SingleUseKeyName of bytes
  | PKeyName
  | PasswordName
  | GuidName
  | NonceName
  | AttackerName

type event =
  | PubNonce of bytes

type intfact =
  | FreshBytes of (bytes * usage) (* Nik: Fine likes tuple types to be parenthesized *)
  | SCompKey of key
  | MCompKey of key
  | PrivCompKey of key

let keytobytes kb = match kb with
  | SymKey(k) -> k
  | AsymPrivKey(k) -> k
  | AsymPubKey(k) -> k

let symkeytobytes kb = match kb with
  | SymKey(k) -> k
  | _ -> failwith "not a symmetric key"

let symkey k = SymKey(k)
let asympubkey k = AsymPubKey(k)
let asymprivkey k = AsymPrivKey(k)
let asympub k = AsymPubKey(utf8 k)
let asympriv k = AsymPrivKey(utf8 k)

#if pv
let freshbytes u s = 
  let n = Pi.name s in
  let b = Fresh n in
    b
#else
(*--- freshbytesBegin *)
let freshbytes u s = 
  let n = Pi.name s in 
  let b = Fresh n in
    Assume (FreshBytes(b,u)); (* Nik: in fine, dynamic assumes are written Assume *)
    b
(*--- freshbytesEnd *)
#endif

let mkKey() = freshbytes SKeyName "key"

let mkKey256() =  mkKey()

let mkPassword() = 
  let b = freshbytes PasswordName "pwd" in
    base64 b

// Nonce generation
let mkbytespub () = freshbytes AttackerName "attacker"
let mkNonce () = freshbytes NonceName "nonce"

let mkNonce256 () = mkNonce() 

let new_keyseed: unit -> unit = fun x -> ()


// Timestamps


// let time () = (base64 (freshbytes "now"), base64 (freshbytes "plusone"))

let time () = 
  let b = freshbytes GuidName "Now" in
  let s = str "PlusOneMinute" in
  let b = base64 b in
   (b,s)

// Hashing

let sha1 x = Bin(Hash(x))

// Symmetric encryption


let sym_encrypt key text = Bin(SymEncrypt(key,text))
let sym_decrypt key msg = match msg with
  | Bin(SymEncrypt((key',text))) when key' = key -> 
      (* expect  (IsEncryption(msg, SymKey(key), text)); *)
      (* expect  (Pubk_Imp_Pub(key, msg)); *)
      text (* Nik: Fine tuple patterns are a bit finicky; 
              added more parenthesis. 
              Flipped order of eq test; helps type inference. *)
  | _ -> failwith "sym_decrypt failed"

// Symmetric signature

let mac key text = 
  let h = Bin(MAC(key,text)) in
//    expect(MAC(SymKey(key),text,h));
  h

let macVerify key text m = match m with
  | Bin(MAC((kk,tt))) when kk = key -> (* Nik: flipped equality *)
     if text = tt then ()
     else failwith "macVerify failed"

// Asymmetric signature

let asym_sign key msg = 
  let s = Bin(AsymSign(key,msg)) in
//    expect(Sign(AsymPrivKey(key),msg,s));
    s

let asym_signature_verify key msg hash = match (key,hash) with
    (Bin(PK(sk)),Bin(AsymSign((sk',m)))) when sk = sk' -> if m = msg then ()
    else failwith "asym_signature_verify: signed values do not match"
  | _ -> failwith "asym_signature_verify failed"
  

// AES encryption

let pad (p:bytes) = 
  let x = utf8 (str "pad") in
    concat x p
let unpad (xp:bytes) = 
  let (x,p) = iconcat xp in 
  let pp = utf8(str "pad") in
    if x = pp then p 
    else failwith "padding incorrect"

let aes_keyseed () = freshbytes KeySeedName "aes_seed"

let aes_keygen ()  = 
  let kb = freshbytes SKeyName "aes_key" in
  SymKey(kb)

let aes_keygen_single b =
  let kb = freshbytes (SingleUseKeyName b) "aes_single_use_key" in
  SymKey(kb)

let aes_keycomp (k:key) =
  (expect (Pub_k(k));
  ()) 

let aes_encrypt k text = 
  match k with 
    | SymKey key -> sym_encrypt key text
    | _ -> failwith "cannot use aes_encrypt with asymmetric key"

let aes_decrypt k msg = 
  match k with 
    | SymKey key -> sym_decrypt key msg
    | _ -> failwith "cannot use aes_decrypt with asymmetric key"

let aes_ccm_encrypt k text = 
  match k with 
    | SymKey key -> sym_encrypt key text
    | _ -> failwith "cannot use aes_encrypt with asymmetric key"

let aes_ccm_decrypt k msg = 
  match k with 
    | SymKey key -> sym_decrypt key msg
    | _ -> failwith "cannot use aes_decrypt with asymmetric key"

#if seals
(* Seal Versions *)
let fail () = failwith "Not Found"
let aes_keygen_seal (): key = 
  let mkn: unit -> bytes = mkNonce in
  let t: (bytes,bytes) Table = table "symkey" fail mkn in
  SealKey (t)

let aes_encrypt_seal k text = 
  match k with 
    | SealKey key -> let (n,e,d) = key in 
      let c = e text in
//	expect (SealEncrypt(k,text,c));
	c
    | _ -> failwith "aes_encrypt expects a seal key"

let aes_decrypt_seal k msg = 
  match k with 
    | SealKey key -> let (n,e,d) = key in 
      let p = d msg in
//	expect (SealEncrypt(k,p,msg));
	p
    | _ -> failwith "aes_encrypt expects a seal key"
#endif

// RSA encryption 

let rsa_pub k = 
  match k with 
    | AsymPrivKey s -> AsymPubKey(Bin(PK s))
    | _ -> failwith "cannot use rsa_pub with symmetric key"

let rsa_keygen () = 
  let kb = freshbytes PKeyName "privkey" in
    AsymPrivKey (kb)

let rsa_keycomp (k:key) = ()

let rsa_encrypt key text = 
  match key with 
    | AsymPubKey k -> 
	let e = Bin(AsymEncrypt(k,text)) in
//	  expect (IsAsymEncryption(e,key,text));
	  e
    | _ -> failwith "cannot use rsa_encrypt with symmetric or private key"
let rsa_decrypt key e = 
  match key,e with 
    | AsymPrivKey k,Bin(AsymEncrypt((pk,text))) when pk = Bin(PK(k)) -> 
//	expect (IsPubKey(AsymPubKey(pk),key));
//	expect (IsAsymEncryption(e,AsymPubKey(pk),text));
	text
    | _ -> failwith "cannot use rsa_decrypt with symmetric or public key"

let rsa_encrypt_oaep key text = 
  match key with 
    | AsymPubKey k -> Bin(AsymEncrypt(k,text))
    | _ -> failwith "cannot use rsa_encrypt with symmetric or private key"
let rsa_decrypt_oaep key e = 
  match key,e with 
    | AsymPrivKey k,Bin(AsymEncrypt((pk,text))) when pk = Bin(PK(k)) -> 
//	expect (IsPubKey(AsymPubKey(pk),key));
//	expect (IsAsymEncryption(e,AsymPubKey(pk),text));
	text
    | _ -> failwith "cannot use rsa_decrypt with symmetric or public key"

// RSA-SHA1

let rsa_sign key t = 
  match key with 
    | AsymPrivKey k -> asym_sign k t
    | _ -> failwith "cannot use rsa_sign with symmetric or public key"

let rsa_verify key t d = 
  match key with 
    | AsymPubKey k -> asym_signature_verify k t d
    | _ -> failwith "cannot use rsa_verify with symmetric or private key"



// HMAC-SHA1

(*--- hmac_keygenBegin *)
let hmac_keygen () = 
  let kb = freshbytes MKeyName "hkey" in
    SymKey(kb)
(*--- hmac_keygenEnd *)

let hmac_keycomp (k:key) = ()

let hmac_keyseed () = freshbytes KeySeedName "hkey_seed" 

let hmacsha1 k text = 
  match k with 
    | SymKey key -> mac key text
    | _ -> failwith "cannot use hmacsha1 with asymmetric key"

let hmacsha1Verify k text sv = 
  match k with 
    | SymKey key -> macVerify key text sv
    | _ -> failwith "cannot use hmacsha1Verify with asymmetric key"


let guid () = 
  let b = freshbytes GuidName "guid" in
    base64 b

// (Password-based) Derived Key generation

let psha1 (k:bytes) (seed:bytes) : key = SymKey (Bin(DerivedKey(k,seed)))

let psha1_aes (k:bytes) (seed:bytes) : key = SymKey (Bin(Data.DerivedSKey(k,seed))) (* Nik: Needed to disambiguate names *)

(* let bar () = (():(x:unit{Smoke1=Smoke2})) *)
