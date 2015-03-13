module ACLs
open String
open List
type file = string

let canWrite = function
  | "C:/temp/tempfile" -> true
  | _ -> false

let publicFile = function 
  | "C:/public/README" -> true
  | _ -> false
  
let canRead (f:file) = 
  canWrite f           (* 1. writeable files are also readable *)
  || publicFile f      (* 2. public files are readable *)
  || f="C:/acls2.fst"  (* and so is this file *)

(* two dangerous primitives *)
assume val read:   file:string{canRead file} -> string
assume val delete: file:string{canWrite file} -> unit

(* some sample files, one of them writable *)
let pwd    = "C:/etc/password"
let readme = "C:/public/README"
let tmp    = "C:/temp/tempfile"

let test () = 
  delete tmp; (* ok *)
//delete pwd; (* type error *)
  let v1 = read tmp in    (* ok, rule 1. *)
  let v2 = read readme in (* ok, rule 2. *)
  () 

(* some higher-order code *)
val rc: file -> ML (unit -> string)
let rc file = 
  if canRead file 
  then (fun () -> read file)
  else failwith "Can't read"


module DSA 
open Array

type bytes = seq byte (* concrete byte arrays *) 
type text  = bytes    (* a type abbreviation, for clarity *)

type nbytes (n:nat) = 
  b:bytes{length b == n} (* fixed-length bytes *)

(* we rely on some external crypto library implementing the DSA standard *)

let keysize = 256 
let tagsize = 20  

type vk = nbytes keysize
type sk = nbytes keysize
assume val sk2vk  : sk -> Tot vk
assume val keygen : unit -> sk

type tag = nbytes tagsize

assume val sign   : sk -> text -> tag 
assume val verify : vk -> text -> tag -> Tot bool 


module SIG 
open Array
open ST 

(* ---- specification *)

(* we attach an authenticated properties to each key, 
   used as a pre-condition for MACing and 
   a postcondition of MAC verification *)

type text = DSA.text
type tag = DSA.tag

type vk = DSA.vk
type sk = 
    | SK : DSA.sk -> sk // abstract 

val sk2vk: sk -> Tot vk
let sk2vk (SK sk) = DSA.sk2vk sk 

opaque type verified : vk -> text -> Type
type vkey (p:(text -> Type)) = k:vk{verified k == p}
type skey (p:(text -> Type)) = k:sk{verified (sk2vk k) == p}

val keygen: p:(text -> Type) -> skey p   
val sign:   p:(text -> Type) -> skey p -> t:text{p t} -> DSA.tag
val verify: p:(text -> Type) -> vkey p -> t:text -> tag -> b:bool{b ==> p t}

(* ---- implementation *)

let keygen (p: (text -> Type)) = 
  let sk = DSA.keygen() in
  let vk = DSA.sk2vk sk in
  assume (verified vk == p);
  SK sk
  
(* to model authentication, we log all genuine calls 
   to MACs; the ideal implementation below uses the 
   log to correct errors. *)

type entry = 
  | Entry : k: vk
         -> t:text{verified k t}
         -> entry

let log = ST.alloc (list entry) [] 

let sign (SK sk) text = 
  log := Entry (DSA.sk2vk sk) text :: !log;
  let tag = DSA.sign sk text in
  tag

let verify vk text tag =
  let verified = DSA.verify vk text tag in 
  let found =
    is_Some 
      (List.find 
        (fun (Entry k text') -> k=vk && text=text')
        !log) in 

  (* plain, concrete implementation (ignoring the log) *) 
//verified           

  (* ideal, error-correcting implementation *) 
  verified && found  

  (* error-detecting implementation for the INT-CMA game *)
//(if verified && not found then win := Some(vk,text,tag)); 

module Cert
open Array
open SIG

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
