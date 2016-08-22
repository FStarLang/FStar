module EtM.AE 

open FStar.Seq
open FStar.SeqProperties
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.Monotonic.RRef


open Platform.Bytes
open CoreCrypto

module CPA = EtM.CPA
module MAC = EtM.MAC

type log_t (r:rid) = Monotonic.Seq.log_t r (CPA.msg * CPA.cipher * MAC.tag)

noeq type key = 
  | Key:  #region:rid -> ke:CPA.key -> km:MAC.key -> log:log_t region -> key 
  (* currently needs flag --__temp_no_proj EtM.AE *)

type cipher = (CPA.cipher * MAC.tag) 

let genPost parent h0 (k:key) h1 =
    modifies Set.empty h0 h1
  /\ extends k.region parent
  /\ fresh_region k.region h0 h1
  /\ m_contains k.log h1
  /\ m_sel h1 k.log == createEmpty

val keygen: parent:rid -> ST key
  (requires (fun _ -> True))
  (ensures  (genPost parent))


let keygen parent =
  let ke = CPA.gen parent in
  let ka = MAC.gen parent in
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  Key #region ke ka log


val encrypt: k:key -> EtM.Plain.plain -> cipher
let encrypt k plain =
  let c = CPA.encrypt k.ke plain in
  (c, MAC.mac k.km c)
  

val decrypt: k:key -> c:cipher -> option EtM.Plain.plain
let decrypt k (c,tag) =
  if MAC.verify k.km c tag
  then ( admit(); Some(CPA.decrypt k.ke c) )
  else None
