module Encrypt_MtE 

module SymEnc = Encrypt_SymEnc

noeq type key (p:Type0) (r:Type) = 
  | Key:  ke:SymEnc.key p r -> MAC.pkey (SymEnc.encrypted ke) -> key p r 
  (* currently needs flag --__temp_no_proj Encrypt_MtE *)

type cipher = (AES.cipher * SHA1.tag) //define abbreviation in MAC.fst


val keygen:  #p:Type0 -> plain: (AES.plain -> p) -> repr:(p -> AES.plain) -> key p AES.plain
let keygen #p plain repr =
  let ke = SymEnc.keygen true plain repr in
  let ka = MAC.keygen (SymEnc.encrypted ke) in
  Key ke ka

val encrypt: #p:Type0 -> k:key p AES.plain -> plain:p -> cipher
let encrypt #p (Key ke ka) plain =
  let c = SymEnc.encrypt ke plain in
  assert(SymEnc.encrypted ke c);
  admit();
  (c, MAC.mac ka c)

val decrypt: #p:Type0 -> k:key p AES.plain -> c:cipher -> option p
let decrypt #p k (c,tag) =
  let (Key ke ka) = k in
  if MAC.verify ka c tag
  then (
    admit();
    assert(SymEnc.encrypted ke c);
    Some(SymEnc.decrypt #p ke c) )
  else None

(* to get functional corretness for EncryptThenMAC, *)
(* we'd also need it for MACs. For later. *)
(* logic type EncText: #p: Type -> #r: Type -> SymEnc.key p r -> MAC.text -> Type (\* an opaque predicate, keeping track of honest encryptions *\) *)
(* val encrypt ... { EncText #p #r k plain c } *)
(* val decrypt ... { forall plain. EncText #p #r k plain c ==> o = Some plain } *)
