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

val mac_log: r:rid -> log_t r -> MAC.log_t r



noeq type key = 
  | Key:  #region:rid -> ke:CPA.key { extends (CPA.Key.region ke) region  } -> km:MAC.key { extends (MAC.Key.region km) region /\  (CPA.Key.region ke) <>(MAC.Key.region km) } -> log:log_t region -> key 
  (* currently needs flag --__temp_no_proj EtM.AE *)


let invariant (h:t) (k:key) = 
  let log = m_sel h k.log in
  let mac_log = m_sel h (MAC.Key.log k.km) in
  let cpa_log = m_sel h (CPA.Key.log k.ke) in
  Seq.length log = Seq.length mac_log /\ 
  Seq.length mac_log = Seq.length cpa_log /\ 
  (forall (i:int). indexable log i ==>
    (let m1,t = Seq.index mac_log i in
    let m2,c = Seq.index cpa_log i in
    m1 = c /\
    Seq.index log i = (m2,c,t) 
    )
  )

let get_log (h:t) (k:key) = 
  m_sel h k.log

let get_mac_log (h:t) (k:key) = 
  m_sel h (MAC.Key.log k.km)

let get_cpa_log (h:t) (k:key) = 
  m_sel h (CPA.Key.log k.ke)


type cipher = (CPA.cipher * MAC.tag) 


let genPost parent h0 (k:key) h1 =
    modifies Set.empty h0 h1
  /\ extends k.region parent
  /\ fresh_region k.region h0 h1
  /\ m_contains k.log h1
  /\ m_sel h1 k.log == createEmpty
  /\ invariant h1 k


val keygen: parent:rid -> ST key
  (requires (fun _ -> True))
  (ensures  (genPost parent))


let keygen parent =
  let region = new_region parent in
  let ke = CPA.gen region in
  let ka = MAC.gen region in
  let log = alloc_mref_seq region createEmpty in
  Key #region ke ka log


val encrypt: k:key -> m:EtM.Plain.plain -> ST cipher
  (requires (fun h0 -> invariant h0 k))
  (ensures  (fun h0 c h1 ->
    (let ilog = m_sel h0 k.log in
     let n = Seq.length ilog in
       modifies (Set.singleton k.region)  h0 h1
     /\ m_contains k.log h1
     /\ m_sel h1 k.log == snoc ilog (m, fst c, snd c)
     /\ witnessed (at_least n (m, fst c, snd c) k.log)
     /\ (invariant h0 k ==> invariant h1 k))))


let encrypt k plain =
  m_recall k.log;
  let h = ST.get () in
  cut (Seq.length (get_mac_log h k) = Seq.length (get_cpa_log h k));
  let c = CPA.encrypt k.ke plain in
  let t = MAC.mac k.km c in
  m_recall (MAC.Key.log k.km);
  m_recall (CPA.Key.log k.ke);
  let h = ST.get () in
  cut (Seq.index (get_mac_log h k) (Seq.length (get_mac_log h k)-1) = (c,t));
  cut (Seq.length (get_mac_log h k) = Seq.length (get_cpa_log h k));
  admit()
  write_at_end k.log (plain,c,t);
  (* lemma_slice_snoc (get_log h k) 0 (Seq.length (get_log h k));  *)
  (* lemma_slice_snoc (get_mac_log h k) 0 (Seq.length (get_mac_log h k)); *)
  (* lemma_slice_snoc (get_cpa_log h k) 0 (Seq.length (get_cpa_log h k)); *)
  let h = ST.get () in
  assert (Seq.index (get_log h k) (Seq.length (get_log h k)-1) = (plain,c,t)); 
  admit()
  (c, t)
   
  
val decrypt: k:key -> c:cipher -> option EtM.Plain.plain
let decrypt k (c,tag) =
  if MAC.verify k.km c tag
  then (
  Some(CPA.decrypt k.ke c) 
  )
  else None
