(* our encryption module is parameterized by a "native" RSA-OAEP
   implementation, available at least for F#/.NET *)

(* I am trying to capture functional correctness, which we did not
   have with F7; otherwise most refinements can be ignored.

   I think this would require coding "events" as membership of
   increasing mutable lists, possibly too advanced for a tutorial *)

module RSA
assume type pkey
assume type skey
type bytes = list byte
type nbytes (n:nat) = b:bytes{List.length b == n}
assume val plainsize  : nat
assume val ciphersize : nat
type plain   = nbytes plainsize
type cipher  = nbytes ciphersize

type keypair = pkey * skey                         
assume val generated : keypair -> Tot bool

assume val gen: unit -> x:keypair{generated x}
assume val dec: skey -> cipher -> Tot (option plain)  (* this function is pure *) 
assume val enc: pk:pkey -> t:plain -> c:cipher { forall sk. generated (pk, sk) ==> dec sk c=Some t }  (* functional correctness *) 
assume val pkbytes: pkey -> bytes
assume val dummy: plain 

module Plain 
         
(* private  *)type t = RSA.plain
type r = RSA.plain 

(* two pure functions, never called when ideal *)
val repr:    t -> Tot r           
let repr t = t       (* a pure function from t to RSA.plain *)  

val plain: x:r -> Tot (option (y:t{repr y = x}))
let plain t = Some t (* a partial function from RSA.plain to t *)

module CCA2  (* intuitively, parameterized by both Plain and RSA *)
open List

type cipher = RSA.cipher
type entry (ideal:bool) (pk:RSA.pkey) = 
    entry:(RSA.cipher * Plain.t){forall sk. (RSA.generated (pk,sk) && not ideal)
                                  ==> RSA.dec sk (fst entry) = Some (Plain.repr (snd entry))}
                                                           (* may consider making plain/repr identities to simplify this *)

val foo : int -> Tot int
let foo : int -> Tot int = failwith ""

val forget: t:Type
            -> p:(t -> Type)
            -> option (x:t{p x}) 
            -> Tot (option t)
let forget = function
  | Some x -> Some x
  | None -> None


let cca2 (ideal:bool) = 
  (* the next step will be to deal with multiple keys. *)
  let pk, sk = RSA.gen ()  in
  let log : ref (list (entry ideal pk)) = ST.alloc [] in

  let enc : Plain.t -> RSA.cipher = fun t -> 
    let t' = if ideal then RSA.dummy else Plain.repr t in
    let c = RSA.enc pk t' in
    (* log := (c,t)::!log;   *)
    c  in

  let dec : RSA.cipher -> option (Plain.t) = fun c ->  
    match (* assoc c !log *) None with
    | Some t when ideal -> Some(t) 
    | _       -> 
       match RSA.dec sk c with 
       | Some(t') -> forget (Plain.plain t')
       | None     -> None in

  pk, enc, dec
  

