
module AES (* concrete implementation of a one-block symmetric cipher *)
open Array

type bytes = MAC.bytes // TODO unclear why we need this instead of seq byte
type nbytes (n:nat) = b:bytes{length b == n}

let blocksize = 32 (* 256 bits *)

type plain  = nbytes blocksize

type cipher = nbytes (2 * blocksize)  (* including IV *)

let keysize = 16 (* 128 bits *)
type key = nbytes keysize 

assume val dummy: plain

assume val generated : key -> Tot bool

assume val gen: unit -> key 
assume val dec: key -> cipher -> Tot plain                    (* this function is pure & complete *)  
assume val enc: k:key -> p:plain -> c:cipher { dec k c = p }  (* this function is not pure (IV); the refinement captures functional correctness *) 


(* -------------------------------------------------------------------------------- *)

module SymEnc (* a multi-key symmetric variant; for simplicity: (1) only using AES above; and (2) parsing is complete *)

type r = AES.plain

(* CPA variant: *) 
opaque type Encrypted: #p: Type -> #k: Type -> k -> MAC.bytes -> Type    (* an opaque predicate, keeping track of honest encryptions *)

type cipher (p:Type) (k:Type) (key:k) = c:AES.cipher { Encrypted key c }    (* TODO why do I need explicit implicits?; NS: you don't seem to need it *)

type keyT: Type -> Type = 
  | Ideal    : p:Type -> AES.key -> i:int -> keyT p (* maybe no need to keep plain/repr around *)
  | Concrete : p:Type -> AES.key -> i:int -> keyT p  

type scheme: Type -> Type =
  | Scheme: p: Type -> k:Type -> 
             keyrepr: (k -> AES.key) -> 
             keygen:  (bool -> k) ->   
             encrypt: (key:k -> p -> cipher p k key) ->
             decrypt: (key:k -> cipher p k key -> p) -> scheme p 

val create: p: Type -> plain: (r -> p) -> repr: (p -> r) -> scheme p 

type entry (p:Type) (k:Type) = 
  | Entry : key:k -> c:cipher p k key -> plain:p -> entry p k

(*
let create (p:Type) plain repr = 
  let c = ST.alloc 0 in
  let log : ref (list (entry p (keyT p))) = ST.alloc [] in
  let keygen : bool -> keyT p = fun safe ->
    let i = !c in
    c := !c + 1;
    let kv = AES.gen() in
    if safe
    then Ideal    p kv i 
    else Concrete p kv i in

  let keyrepr k = 
    match k with 
    | Ideal kv _ -> failwith "no way!"
    | Concrete kv _ -> kv in

  let encrypt: (key:keyT p -> p -> cipher p (keyT p) key) = fun k text ->
    let c = 
      match k with
      | Ideal kv _ -> let c = AES.enc kv AES.dummy in
                        log := Entry k c text :: !log; 
                        c
      | Concrete kv _ -> AES.enc kv (repr text) in
    assume (Encrypted k c); 
    c
   
  in

  let decrypt: key:keyT p -> cipher p (keyT p) key -> p = fun k c ->
    match k with 
    | Ideal kv _ -> (match List.find (fun (Entry k' c' _) -> k=k' && c= c') !log with 
                      | Some e -> Entry.plain e
                      | _ -> failwith "never")
    | Concrete kv _ -> plain (AES.dec kv c)  
  in

  Scheme p (keyT p) keyrepr keygen encrypt decrypt
 *)
   
module SampleEncrypt
open SymEnc
let plain (x:AES.plain) = x 
let repr (x:AES.plain) = x 

let test() =
  let p = failwith "nice bytes" in
  let Scheme keyrepr keygen encrypt decrypt = SymEnc.create (AES.plain) plain repr in 
  let k0 = keygen true in
  let k1 = keygen true in
  let c = encrypt k0 p in
  let p' = decrypt k0 c in
//assert( p == p');                   // this succeeds, by functional correctness
  (* let p'' = SymEnc.decrypt k1 c in  // this rightfully triggers an error *)
  ()


module EncryptThenMAC 
open SymEnc

type p = AES.plain

let plain (x:AES.plain) = x 
let repr (x:AES.plain) = x 
 
let s = SymEnc.create p plain repr
type k = Scheme.k s 

type k2 = 
  | Key:  ke:k -> MAC.pkey (SymEnc.Encrypted #p #k ke) -> k2

type cipher = (AES.cipher * MAC.tag)

val decrypt: key:k2 -> cipher -> option p
let decrypt (Key ke ka) (c,tag) =
  if MAC.verify ka c tag
  then Some(Scheme.decrypt s ke c)
  else None

val keygen: unit -> k2
let keygen() =
  let ke = Scheme.keygen s true in
  let ka = MAC.keygen (SymEnc.Encrypted #p #k ke) in
  Key ke ka

val encrypt: key:k2 -> plain:p -> cipher
let encrypt (Key ke ka) plain =
  let c = Scheme.encrypt s ke plain in
  (c, MAC.mac ka c)

