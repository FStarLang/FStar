(* 
   Exercising:
    -- indexed types
    -- existential types
    -- and refinements, of course
*)
module AES (* concrete implementation of a one-block symmetric cipher *)
open Array

type bytes = seq byte
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

open ST
open List

type r = AES.plain

(* CPA variant: *) 
opaque type Encrypted: #k: Type -> p:Type -> k -> AES.bytes -> Type         (* an opaque predicate, keeping track of honest encryptions *)
type cipher (p:Type) (k:Type) (key:k) = c:AES.cipher { Encrypted p key c }  

type keyT: Type -> Type = 
  | Ideal    : p:Type -> AES.key -> i:int -> keyT p (* maybe no need to keep plain/repr around *)
  | Concrete : p:Type -> AES.key -> i:int -> keyT p  

type scheme: Type -> Type =
  | Scheme:  p:Type -> k:Type -> 
             keyrepr: (k -> AES.key) -> 
             keygen:  (bool -> k) ->   
             encrypt: (key:k -> p -> cipher p k key) ->
             decrypt: (key:k -> cipher p k key -> p) -> 
             scheme p 



type entry (p:Type) (k:Type) = 
  | Entry : key:k -> c:cipher p k key -> plain:p -> entry p k

val create: p: Type -> plain: (r -> p) -> repr: (p -> r) -> scheme p 
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

  let keyrepr k : AES.key = 
    match k with 
    | Ideal kv _ -> failwith "no way!"
    | Concrete kv _ -> kv in

  let encrypt: (k:keyT p -> p -> cipher p (keyT p) k) = fun k text ->
    match k with
    | Ideal kv _ -> 
       let c = AES.enc kv AES.dummy in
       assume (Encrypted p k c); 
       log := Entry k c text :: !log; 
       c

    | Concrete kv _ -> 
       let rep = repr text in    (* NS: need the let-binding because repr is impure and we can't substitute it in the type of 'enc' *) 
       let c = AES.enc kv rep in
       assume (Encrypted p k c); 
       c in
    

  let decrypt: key:keyT p -> cipher p (keyT p) key -> p = fun k c ->
    match k with 
    | Ideal kv _ -> (match List.find (fun (Entry k' c' _) -> k=k' && c= c') !log with 
                     | Some e -> Entry.plain e
                     | _ -> failwith "never")
    | Concrete kv _ -> plain (AES.dec kv c)  in

  Scheme p (keyT p) keyrepr keygen encrypt decrypt
   
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
  //assert( p == p');           // this should eventually succeed, once we prove functional correctness
  (* let p'' = decrypt k1 c in     // this rightfully triggers an error *)
  ()


module MAC3

open Array
type bytes = seq byte (* concrete byte arrays *) 
type text  = bytes    (* a type abbreviation, for clarity *)

type nbytes (n:nat) = b:bytes{length b == n} (* fixed-length bytes *)

let keysize = 16 (* these are the sizes for SHA1 *) 
let macsize = 20  
type key = nbytes keysize
type tag = nbytes macsize

(* we rely on some external crypto library implementing HMAC-SHA1 *)

assume val sha1: key -> text -> Tot tag 

(* to verify, we simply recompute & compare *) 

val sha1verify: key -> text -> tag -> Tot bool
let sha1verify k txt tag = (sha1 k txt = tag)

(* we attach an authenticated properties to each key, 
   used as a pre-condition for MACing and 
   a postcondition of MAC verification *)

opaque type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = k:key{key_prop k == p}

assume val leak: k:key { forall t. key_prop k t } -> bytes 
assume val leaked: k:key -> b:bool { b ==> (forall t. key_prop k t) }   

(* this function returns the key bytes, and marks the key as corrupted *)

assume val keygen: p:(text -> Type) -> pkey p

val mac:    k:key -> t:text{key_prop k t} -> tag
val verify: k:key -> t:text -> tag -> b:bool{b ==> key_prop k t}

(* to model authentication, we log all genuine calls to MACs *) 

(* the ideal implementation below uses a global log *)

type entry = 
  | Entry : k:key
         -> t:text{key_prop k t}
         -> m:tag
         -> entry

let log = ST.alloc (list entry) [] 

let mac k t = 
  let m = sha1 k t in
  log := Entry k t m :: !log;
  m

let verify k text tag =
  let verified = sha1verify k text tag in 
  let found    = is_Some(List.find (function (Entry k' text' tag') -> k=k' && text=text' (*CTXT: && tag=tag' *) ) !log) in 

  (* plain, concrete implementation (ignoring the log) *) 
//verified           

  (* ideal, error-correcting implementation *) 
  verified && (found || leaked k ) 

  (* error-detecting implementation for the INT-CMA-LEAK game
//if verified && not (found || leaked k) then win:= Some(k,text,tag);
//verified 



module EncryptThenMAC

open SymEnc
open MAC3

type p = AES.plain

let plain (x:AES.plain) = x
let repr (x:AES.plain) = x
 
let s = SymEnc.create p plain repr
type k = Scheme.k s

type k2 =
  | Key:  ke:k -> MAC3.pkey (SymEnc.Encrypted (Scheme.p s) ke) -> k2

type cipher = (AES.cipher * MAC3.tag)

val decrypt: key:k2 -> cipher -> option (Scheme.p s)
let decrypt (Key ke ka) (c,tag) =
  if MAC3.verify ka c tag
  then Some(Scheme.decrypt s ke c)
  else None

val keygen: unit -> k2
let keygen() =
  let ke = Scheme.keygen s true in
  let ka = MAC3.keygen (SymEnc.Encrypted (Scheme.p s) ke) in
  Key ke ka

val encrypt: key:k2 -> plain:Scheme.p s -> cipher
let encrypt (Key ke ka) plain =
  let c = Scheme.encrypt s ke plain in
  (c, MAC3.mac ka c)

