
module AES (* concrete implementation of a one-block symmetric cipher *)
open Array

type bytes = MAC.bytes // TODO unclear why we need this instead of seq byte
type nbytes (n:nat) = b:bytes{length b == n}

let blocksize = 32 (* 256 bits *)

type plain  = nbytes blocksize

type cipher = nbytes (2 * blocksize)  (* including IV *)

let keysize = 16 (* 128 bits *)
type key = nbytes keysize 

assume val generated : key -> Tot bool

assume val gen: unit -> key 
assume val dec: key -> cipher -> Tot plain                    (* this function is pure & complete *)  
assume val enc: k:key -> p:plain -> c:cipher { dec k c = p }  (* this function is not pure (IV); the refinement captures functional correctness *) 


(* -------------------------------------------------------------------------------- *)

module SymEnc (* a multi-key symmetric variant; for simplicity: (1) only using AES above; and (2) parsing is complete *)

type bytes = MAC.bytes

(* TODO: we get the index from a counter; 
   In the crypto argument, we rely on the fact that we only construct keys once for each i. *)

assume type keyval (p:Type) (r:Type) (i:int)

(* TODO: I need something like this, can't get it accepted 
opaque type keyval (p:Type) (r:Type) (i:int) = 
  | Ideal    : plain: (r -> p) -> repr: (p -> r) -> AES.key -> keyval p r i   (* maybe no need to keep plain/repr around *)
  | Concrete : plain: (r -> p) -> repr: (p -> r) -> AES.key -> keyval p r i 
 *)

type key (p:Type) (r:Type) = i:int * keyval p r i (* so that the index i can be kept implicit *)

(* CPA variant: *) 

logic type Encrypted: #p: Type -> #r: Type -> key p r -> MAC.bytes -> Type (* an opaque predicate, keeping track of honest encryptions *)

type cipher (p:Type) (r:Type) (k: key p r) = c: MAC.bytes (* should be: AES.cipher *) { Encrypted #p #r k c }    (* TODO why do I need explicit implicits? *)

assume val keygen:  #p:Type -> #r:Type -> plain:(r -> p) -> repr:(p -> r) -> key p r 
assume val decrypt: #p:Type -> #r:Type -> k:key p r -> cipher p r k -> Tot p
assume val encrypt: #p:Type -> #r:Type -> k:key p r -> plain: p -> c:cipher p r k { decrypt k c = plain }

(*

(* TODO: implementation *)

//let c = ref 0

let keygen safe plain repr = 
//let i = !c in
//c := !c + 1; 
  let i = 3 in
  let k = AES.gen() in 
  if safe 
  then i, Ideal   (plain,repr,k) 
  else i, Concrete(plain,repr,k)

let decrypt (i,Ideal(plain,repr,kv)) c = AES.dec kv c
let encrypt (i,Ideal(plain,repr,kv)) p = AES.enc kv p


(* below is for CCA2, with just bytes as ciphers. *)

assume val decrypt: p:Type -> r:Type -> k:key p r -> c: cipher -> option p 
assume val encrypt: p:Type -> r:Type -> k:key p r -> plain: p -> c:cipher { decrypt p r k c = Some plain }

(* for CPA, ciphers should not be forgeable, but we need to be able to treat sbytes as cipher after checking e.g. a MAC *)

assume val decrypt: p:Type -> r:Type -> k:skey p r -> c: cipher p r k -> option p 
assume val encrypt: p:Type -> r:Type -> k:skey p r -> plain: p -> c:cipher p r k { decrypt p r k c = plain }
*)

(* -------------------------------------------------------------------------------- *)
module SampleEncrypt

let plain (x:AES.plain) = x 
let repr (x:AES.plain) = x 

let test() = 
  let p = failwith "nice bytes" in
  let k0 = SymEnc.keygen plain repr in
  let k1 = SymEnc.keygen plain repr in
  let c = SymEnc.encrypt k0 p in
  let p' = SymEnc.decrypt k0 c in 
  assert( p == p');                   // this succeeds, by functional correctness
//  let p'' = SymEnc.decrypt k1 c in  // this rightfully triggers an error
  ()


module EncryptThenMAC 

type key (p:Type) (r:Type) = 
  | Key:  ke:SymEnc.key p r -> MAC.pkey (fun c -> SymEnc.Encrypted ke c) -> key p r 

type cipher = AES.cipher * MAC.tag

val decrypt: #p:Type -> #r:Type -> k:key p r -> c:cipher -> option p

let decrypt (Key ke ka) (c,t) =
  if MAC.verify ka t c 
  then Some(SymEnc.decrypt ke c) 
  else None

// to get functional corretness for EncryptThenMAC, 
// we'd also need it for MACs. For later.
// logic type EncText: #p: Type -> #r: Type -> SymEnc.key p r -> MAC.text -> Type (* an opaque predicate, keeping track of honest encryptions *)
// val encrypt ... { EncText #p #r k plain c } 
// val decrypt ... { forall plain. EncText #p #r k plain c ==> o = Some plain } 

val encrypt: #p:Type -> #r:Type -> k:key p r -> plain: p -> cipher 

val keygen:  p:Type -> r:Type -> plain: (r -> p) -> repr:(p -> r) -> key p r 
let keygen plain repr = 
  let ke = SymEnc.keygen plain repr in
  let ka = MAC.keygen (fun c -> SymEnc.Encrypted ke c) in
  Key ke ka

let encrypt (Key ke ka) plain = 
  let c = SymEnc.encrypt ke plain in
  (c, MAC.mac ka c)

