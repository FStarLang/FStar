module Cert.Cert
open Array
open Cert.Sig

type bytes = seq byte
type user = bytes
type mail = bytes

assume val format: list bytes -> Tot bytes  
assume val parse: b:bytes -> Tot(option (s: list bytes {format s = b} ))

opaque type sent: user -> mail -> Type // application semantics
opaque type certified (text: bytes) = 
    (forall (u:user). 
     forall (k:vk).
        text = format [u; k] ==> 
            verified k == (fun (m: mail) -> sent u m ))

// how to generalize to recursive certificate chains?
// the signed text for delegation would be [INTER; id; k]

val sk0: skey certified 
let sk0 = keygen certified
let vk0 = sk2vk sk0
    
let register user =
    assume ( 
        forall (a: list bytes) (b: list bytes).
            format a = format b ==> a = b );
    let sk = keygen (sent user) in
    let vk = sk2vk sk in
    let text = format [user; vk] in
    assert (certified text); // helping the prover
    let cert = format [text ; sign sk0 text] in
    let send (m:mail { sent user m }) = 
        let tag = sign sk m in
        [ m; cert; tag ] in
    cert, send
    
// let delegate admin = ...

type verified_mail = 
    | ReceivedFrom: u:user -> m:mail { sent u m } -> verified_mail
    
val checkmail: bytes -> verified_mail
let checkmail inbox = 
    (match parse inbox with 
     | Some [ mail; cert; mtag ] ->
      (match parse cert with
      | Some [ ctxt; ctag ] ->
        (match parse ctxt with
        | Some [ sender; vk ] -> 
            if verify vk0 ctxt ctag && verify vk mail mtag 
            then ReceivedFrom sender mail 
            else failwith "bad signature"
        | _ -> failwith "bad certificate text")
      | _ -> failwith "bad certificate format")
    | _ -> failwith "bad message format")
