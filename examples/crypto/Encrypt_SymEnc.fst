module Encrypt_SymEnc (* a multi-key symmetric variant; for simplicity: (1) only using AES above; and (2) parsing is complete *)
open FStar.All
open FStar.ST
type bytes = Platform.Bytes.bytes

(* TODO: we get the index from a counter; 
   In the crypto argument, we rely on the fact that we only construct keys once for each i. *)

noeq type key (p:Type) (r:Type) = 
  | Ideal    : plain: (r -> p) -> repr: (p -> r) -> AES.key -> i:int -> key p r (* maybe no need to keep plain/repr around *)
  | Concrete : plain: (r -> p) -> repr: (p -> r) -> AES.key -> i:int -> key p r  

assume HasEq_key: hasEq (key (p:Type) (r:Type))


// type key (p:Type) (r:Type) = i:int * keyval p r i (* so that the index i can be kept implicit *)
    
(* CPA variant: *) 
assume type encrypted: #p: Type -> #r: Type -> key p r -> bytes -> Type    (* an opaque predicate, keeping track of honest encryptions *)

type cipher (p:Type) (r:Type) (k: key p r) = c:AES.cipher { encrypted k c }    
(* TODO why do I need explicit implicits?; NS: you don't seem to need it *)
val keygen:  #p:Type0 -> bool -> plain:(AES.plain -> p) -> repr:(p -> AES.plain) -> ML (key p AES.plain)
val decrypt: #p:Type0 -> k:key p AES.plain -> cipher p AES.plain k -> ML p
val encrypt: #p:Type0 -> k:key p AES.plain -> plain: p -> ML (cipher p AES.plain k)


(* TODO: implementation *)

let c :ref nat = ST.alloc 0

let keygen #p safe plain repr =
  let i = !c in
  c := !c + 1;
  let k = AES.gen() in
  if safe
  then Ideal    plain repr k i 
  else Concrete plain repr k i

noeq type entry (#p:Type0): Type0 = 
  | Entry : k:key p AES.plain -> c:cipher p AES.plain k -> plain:p -> entry #p

let log (p:Type): St (ref (list (entry #p))) = ST.alloc [] 

let encrypt #p k text = 
  match k with 
  | Ideal plain repr kv _ -> let c = AES.enc kv AES.dummy in
                           let l = log p in
			   admit(); (* MK *)
                           l := Entry k c text :: !l; 
                           c
  | Concrete plain repr kv _ -> let rtext = (repr text) in admit(); (* MK *) AES.enc kv rtext


let decrypt #p k c = 
  match k with 
  | Ideal plain repr kv _ ->
    let f (Entry k' c' _) = c=c' in
    (match List.Tot.find f !(log p) with
     | Some (Entry _ _ p) -> p
     | _ -> failwith "never")
  | Concrete plain repr kv _ -> plain (AES.dec kv c)

(* (\* below is for CCA2, with just bytes as ciphers. *\) *)

(* assume val decrypt: p:Type -> r:Type -> k:key p r -> c: cipher -> option p  *)
(* assume val encrypt: p:Type -> r:Type -> k:key p r -> plain: p -> c:cipher { decrypt p r k c = Some plain } *)

(* (\* for CPA, ciphers should not be forgeable, but we need to be able to treat sbytes as cipher after checking e.g. a MAC *\) *)

(* assume val decrypt: p:Type -> r:Type -> k:skey p r -> c: cipher p r k -> option p  *)
(* assume val encrypt: p:Type -> r:Type -> k:skey p r -> plain: p -> c:cipher p r k { decrypt p r k c = plain } *)
