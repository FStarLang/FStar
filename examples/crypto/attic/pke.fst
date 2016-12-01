(* our encryption module is parameterized by a "native" RSA-OAEP
   implementation, available at least for F#/.NET *)

(* I am trying to capture functional correctness, which we did not
   have with F7; otherwise most refinements can be ignored.

   We could further code "events" as membership of increasing mutable
   lists, but this is possibly too advanced for a tutorial *)

module RSA (* trustedd implementation of RSA-OAEP *) 

assume type pkey
assume type skey
type bytes = list byte
type nbytes (n:nat) = b:bytes{List.length b == n}
assume val plainsize  : nat
assume val ciphersize : nat
assume val pksize : nat
type plain  = nbytes plainsize
type cipher = nbytes ciphersize

type keypair = pkey * skey                         
assume val generated : keypair -> Tot bool

assume val gen: unit -> x:keypair{generated x}
assume val dec: skey -> cipher -> Tot (option plain)  (* this function is pure *) 
assume val enc: pk:pkey -> t:plain -> c:cipher { forall sk. generated (pk, sk) ==> dec sk c=Some t }  (* functional correctness *) 
assume val pkbytes: pkey -> nbytes pksize
assume val dummy: plain 


module Plain 
         
(* private *)
type t = RSA.plain
type r = RSA.plain 

(* two pure functions, never called when ideal *)
val repr:    t -> Tot r           
let repr t = t  (* a pure function from t to RSA.plain *)  

val plain: x:r -> Pure (option t) (requires True) (ensures (fun o -> Some? o /\ repr (Some.v o) = x))
let plain t = Some t (* a partial function from RSA.plain to t *)


module PKE  (* intuitively, parametric in both Plain and RSA *)
open List

let pksize     = RSA.pksize
let ciphersize = RSA.ciphersize
type cipher = RSA.cipher

type entry = 
(* indexing entry with ideal and pk triggers some bugs; meanwhile, using a simple type *)
  | Entry : ideal: bool
         -> pk':RSA.pkey
         -> c:RSA.cipher
         -> p:Plain.t{forall sk. (RSA.generated (pk',sk) && not ideal)
                       ==> RSA.dec sk c = Some (Plain.repr p)} (* may consider making plain/repr identities to simplify this *)
         -> entry

val ideal: bool
let ideal = true

val encrypt: Plain.t -> RSA.cipher 
val decrypt: RSA.cipher -> option (Plain.t) 

let keys = RSA.gen ()  
let pk = fst keys
let sk = snd keys

let log : ref (list entry) = ST.alloc [] 

let encrypt plain =
    let repr = if ideal then RSA.dummy else Plain.repr plain in
    let c = RSA.enc pk repr in
    log := Entry ideal pk c plain::!log;
    c  

let decrypt cipher = 
    match List.find (function Entry _ _ c _ -> c=cipher) !log with
    | Some t when ideal -> Some(Entry.p t)
    | _  -> 
      (match RSA.dec sk cipher with 
      | Some(t') -> Plain.plain t'
      | None     -> None )
  
