module MtE.AE 

module CPA = MtE.CPA


noeq type key = 
  | Key:  ke:CPA.key -> mk:MAC.pkey (CPA.encrypted ke) -> key 
  (* currently needs flag --__temp_no_proj Encrypt_MtE *)

type cipher = (AES.cipher * SHA1.tag) //define abbreviation in MAC.fst


val keygen: unit -> key
let keygen () =
  let ke = CPA.keygen () in
  let ka = MAC.keygen (CPA.encrypted ke) in
  Key ke ka

val encrypt: k:key -> MtE.Plain.plain -> cipher
let encrypt (Key ke ka) plain =
  let c = CPA.encrypt ke plain in
  assert(CPA.encrypted ke c);
  admit();
  (c, MAC.mac ka c)

val decrypt: k:key -> c:cipher -> option MtE.Plain.plain
let decrypt k (c,tag) =
  let (Key ke ka) = k in
  if MAC.verify ka c tag
  then (
    admit();
    assert(CPA.encrypted ke c);
    Some(CPA.decrypt ke c) )
  else None
