module MacIdeal 
open Array
type bytes    = seq byte
type text     = bytes
type nbytes (n:nat) = b:bytes{length b == n}
let macsize = 20
let keysize = 16
type mac_t = nbytes macsize
type key   = nbytes keysize

type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = k:key{key_prop k == p}

assume val new_key: p:(text -> Type)
                 -> pkey p

assume val hmac_sha1: key -> text -> Tot mac_t

type entry = 
  | Entry : k:key
         -> t:text{key_prop k t}
         -> m:mac_t
         -> entry

assume val log : ref (list entry)

val mac: k:key
      -> t:text{key_prop k t}
      -> mac_t
let mac k t = 
  let m = hmac_sha1 k t in
  log := Entry k t m :: !log;
  m

val verify: k:key
         -> t:text 
         -> mac_t 
         -> b:bool{b ==> key_prop k t}
let verify k t m = 
  let found = List.find (function (Entry k' t' _) -> k=k' && t=t') !log in
  is_Some found



(* module Prelude *)
(* assume val randomBytes: n:nat -> b:bytes{length b == n} *)
(* val find: f:(x:'a -> Tot bool) *)
(*         -> list 'a *)
(*         -> Tot (option (x:'a{f x == true})) *)


(* module Mac *)
(* open Prelude *)
(* open Array *)
(* open ListLemmas *)

(* type bytes    = seq byte *)
(* type text     = bytes *)
(* type nbytes (n:nat) = b:bytes{length b == n} *)
(* let macsize = 20 *)
(* let keysize = 16 *)
(* type mac      = nbytes macsize *)
(* type key = nbytes keysize *)

(* (\* If you want equality on keys, while erasing the 'P index, you need *)
(* to be careful. *)

(*   (K Good b = K Bad b) decided by comparing only the b's *)
(*   then you may conclude Good=Bad ... which is False.  *)

(*   So, either:  *)
(*     1. disable equality on types with erased components (a bit drastic) *)

(*     2. allow equality after erasure if  *)
(*           [[v1:t1]] = v1' /\ [[v2:t2]]=v2' *)
(*         ==> (v1'=v2' ==> v1=v2) *)
  

 

(*  *\) *)
(* (\* type key : (text => Type) => Type = *\) *)
(* (\*   | K : 'P:(text => Type) -> bytes -> key 'P *\) *)

(* (\* type f : bytes => text => Type *\) *)

(* type key : (text -> Type) -> Type = *)
(*   | K : p:(text -> Type) -> b:key -> key p *)


(* assume val hmac_sha1: key -> text -> mac_t *)

(* val gen: unit -> key 'P *)
(* let gen () = randomBytes keysize *)

(* val mac: k:key 'P -> t:text{'P t} -> mac_t *)
(* let mac k t = hmac_sha1 k t *)

(* (\* concrete *\) *)
(* val verify: k:key 'P -> t:text -> mac_t -> b:bool{b==true ==> 'P t} *)
(* let verify k t m = hmac_sha1 k t = m *)

(* (\*********************************************************************************\) *)
