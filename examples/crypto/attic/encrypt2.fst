module SymEnc (* a multi-key symmetric variant; for simplicity, we fix (p, r, plain, repr) and use AES above *)
open Array

(* parametric in these: *)

type r = AES.plain

assume type p 
assume val plain: r -> p
assume val repr: p -> r
(*
type p = AES.plain
let plain (x:AES.plain) = x 
let repr (x:AES.plain) = x 
*)

type bytes = seq byte

(* we get the index from a counter; In the crypto argument, we rely on
   the fact that we only construct keys once for each i. *)

(*private*) type key = | Key: ideal: bool -> i:int -> kv:AES.key -> key 

(* an predicate keeping track of honest encryptions *)
    
opaque type Encrypted: key -> bytes -> Type 

type cipher (k: key) = c:AES.cipher { Encrypted k c }
val ciphersize: nat
let ciphersize = AES.ciphersize

val keygen:  b:bool -> k:key { Key.ideal k = b } 
val keyrepr: k:key { Key.ideal k = false } -> Tot AES.key
val decrypt: k:key -> cipher k -> p
val encrypt: k:key -> plain: p -> cipher k 

let c = ST.alloc 0
let keygen safe =
  let i = !c in
  c := !c + 1;
  let k = AES.gen() in
  Key safe i k

let keyrepr k = Key.kv k

type entry = | Entry : k:key -> c:cipher k -> plain:p -> entry

let log : ref (list entry) = ST.alloc [] 

let encrypt k text = 
  let r = if Key.ideal k then AES.dummy else repr text in 
  let c = AES.enc (Key.kv k) r in
  assume (Encrypted k c);
  log := Entry k c text :: !log; 
  c

let decrypt k c = 
  match List.find (fun (Entry k' c' _) -> k=k' && c=c') !log with 
  | Some e -> Entry.plain e 
  | _ -> failwith "never actually decrypting" 

(* typing this function relies on --full_context_dependency *)



module SampleEncrypt

let test() =
  let p = failwith "nice bytes" in
  let k0 = SymEnc.keygen true in
  let k1 = SymEnc.keygen true in
  let c = SymEnc.encrypt k0 p in
  let p' = SymEnc.decrypt k0 c in
//assert( p == p');                   // this succeeds, by functional correctness
  (* let p'' = SymEnc.decrypt k1 c in  // this rightfully triggers an error *)
  ()


module EncryptThenMAC 

type key = | Key: 
  ke: SymEnc.key -> 
  ka: MAC.pkey (SymEnc.Encrypted ke) -> key 

type plain = SymEnc.p
type cipher = (AES.cipher * SHA1.tag)

val keygen: unit -> key 
val encrypt: k:key -> plain -> cipher
val decrypt: k:key -> cipher -> option plain

let decrypt (Key ke ka) (c,tag) =
  if MAC.verify ka c tag
  then Some(SymEnc.decrypt ke c)
  else None

let keygen () =
  let ke = SymEnc.keygen true in
  let ka = MAC.keygen (SymEnc.Encrypted ke) in
  Key ke ka

let encrypt (Key ke ka) plain =
  let c = SymEnc.encrypt ke plain in
  (c, MAC.mac ka c)
