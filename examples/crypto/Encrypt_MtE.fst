module Encrypt_MtE 


type key (p:Type) (r:Type) = 
  | Key:  ke:Encrypt_SymEnc.key p r -> MAC.pkey (SymEnc.encrypted ke) -> key p r 

type cipher = (AES.cipher * SHA1.tag) //define abbreviation in MAC.fst


val decrypt: #p:Type -> k:key p AES.plain -> c:cipher -> option p
let decrypt #p (Key ke ka) (c,tag) =
  if MAC.verify ka c tag
  then Some(SymEnc.decrypt ke c)
  else None

(* to get functional corretness for EncryptThenMAC, *)
(* we'd also need it for MACs. For later. *)
(* logic type EncText: #p: Type -> #r: Type -> SymEnc.key p r -> MAC.text -> Type (\* an opaque predicate, keeping track of honest encryptions *\) *)
(* val encrypt ... { EncText #p #r k plain c } *)
(* val decrypt ... { forall plain. EncText #p #r k plain c ==> o = Some plain } *)

val keygen:  #p:Type -> plain: (AES.plain -> p) -> repr:(p -> AES.plain) -> key p AES.plain
let keygen #p plain repr =
  let ke = SymEnc.keygen true plain repr in
  let ka = MAC.keygen (SymEnc.encrypted ke) in
  Key ke ka

val encrypt: #p:Type -> k:key p AES.plain -> plain:p -> cipher
let encrypt #p (Key ke ka) plain =
  let c = SymEnc.encrypt ke plain in
  (c, MAC.mac ka c)


