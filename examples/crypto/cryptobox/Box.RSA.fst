(* our encryption module is parameterized by a "native" RSA-OAEP
   implementation, available at least for F#/.NET *)

(* I am trying to capture functional correctness, which we did not
   have with F7; otherwise most refinements can be ignored.

   I think this would require coding "events" as membership of
   increasing mutable lists, possibly too advanced for a tutorial *)

(* We should replace this module by an implementation using CoreCrypto, 
   can we use OAEP? *)

module Box.RSA

open FStar.BaseTypes
open FStar.List.Tot

open Platform.Bytes
open CoreCrypto

module B = Platform.Bytes

assume val pk_size : nat
assume val sk_size : nat

type pkey = lbytes pk_size
type skey = lbytes sk_size

let plainsize  = aeadKeySize AES_128_GCM
assume val ciphersize : nat
type plain   = lbytes plainsize
type cipher  = lbytes ciphersize

type keypair = pkey * skey
assume val generated : keypair -> Tot bool

assume val gen: unit -> ST keypair
  (requires (fun h0 -> True))
  (ensures (fun h0 x h1 -> b2t (generated x)))
assume val dec: skey -> cipher -> Tot (option plain)  (* this function is pure *)
assume val enc: pk:pkey -> t:plain -> ST cipher 
  (requires (fun h0 -> True))
  (ensures (fun h0 c h1 -> 
    (forall sk. generated (pk, sk) ==> dec sk c=Some t  (* functional correctness *))
    /\ modifies_none h0 h1
    ))
assume val pkbytes: pkey -> Tot bytes
assume val dummy: plain

