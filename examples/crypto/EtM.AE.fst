module EtM.AE
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef

module MAC = EtM.MAC

open Platform.Bytes
open CoreCrypto
module CPA = EtM.CPA
module MAC = EtM.MAC
module Ideal = EtM.Ideal
module Plain = EtM.Plain

abstract type cipher = (CPA.cipher * MAC.tag)

type rid = FStar.Monotonic.Seq.rid

let log_entry = CPA.msg * cipher
type log_t (r:rid) = m_rref r (seq log_entry) grows

noeq type key =
  | Key:  #region:rid ->
               ke:CPA.key { extends (CPA.Key?.region ke) region  } ->
               km:MAC.key { extends (MAC.Key?.region km) region /\
                 (disjoint( CPA.Key?.region ke) (MAC.Key?.region km)) } ->
               log:log_t region -> key

let get_log (h:mem) (k:key) =
  m_sel h k.log

let get_mac_log (h:mem) (k:key) =
  m_sel h (MAC.Key?.log k.km)

let get_cpa_log (h:mem) (k:key) =
  m_sel h (CPA.Key?.log k.ke)

//Only valid ciphers are mac'd
let mac_only_cpa_ciphers (mac:Seq.seq EtM.MAC.log_entry) (cpa:Seq.seq EtM.CPA.log_entry) =
  forall (c:cipher). {:pattern (Seq.mem c mac)}
     Seq.mem c mac
      <==>
     (exists (p:Plain.plain). Seq.mem (CPA.Entry p (fst c)) cpa)

//AE log abstracts the mac and cpa logs
let mac_and_cpa_refine_ae (ae:Seq.seq log_entry) 
                          (mac:Seq.seq EtM.MAC.log_entry)
                          (cpa:Seq.seq EtM.CPA.log_entry) =
  forall (p:Plain.plain) (c:cipher).{:pattern (Seq.mem (p, c) ae)}
     Seq.mem (p,c) ae
     <==>
     (Seq.mem c mac /\
      Seq.mem (CPA.Entry p (fst c)) cpa)

let invariant (h:mem) (k:key) =
  let log = get_log h k in
  let mac_log = get_mac_log h k in
  let cpa_log = get_cpa_log h k in
  Map.contains h.h k.region /\
  Map.contains h.h (MAC.Key?.region k.km) /\
  Map.contains h.h (CPA.Key?.region k.ke) /\
  Seq.length log = Seq.length mac_log /\
  Seq.length mac_log = Seq.length cpa_log /\
  EtM.CPA.invariant (Key?.ke k) h /\
  mac_only_cpa_ciphers (get_mac_log h k) (get_cpa_log h k) /\
  mac_and_cpa_refine_ae (get_log h k) (get_mac_log h k) (get_cpa_log h k)

let genPost parent h0 (k:key) h1 =
    modifies Set.empty h0 h1
  /\ extends k.region parent
  /\ fresh_region k.region h0.h h1.h
  /\ Map.contains h1.h k.region
  /\ m_contains k.log h1
  /\ m_sel h1 k.log == createEmpty
  /\ invariant h1 k

val keygen: parent:rid -> ST key
  (requires (fun _ -> True))
  (ensures  (genPost parent))

let keygen parent =
  let region = new_region parent in
  let ke = CPA.keygen region in
  let ka = MAC.keygen region in
  let log = alloc_mref_seq region createEmpty in
  Key #region ke ka log

val encrypt: k:key -> m:Plain.plain -> ST cipher
  (requires (fun h0 -> invariant h0 k))
  (ensures  (fun h0 c h1 ->
    (let log0 = get_log h0 k in
     let log1 = get_log h1 k in
     HyperHeap.modifies (Set.singleton k.region)  h0.h h1.h
     /\ invariant h1 k
     /\ log1 == snoc log0 (m, c))))
     
     // /\ witnessed (at_least (Seq.length log0) (m, c) k.log)
     // /\ invariant h1 k)))

// #set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 100"
let encrypt k plain =
  let c = CPA.encrypt k.ke plain in
  let t = MAC.mac k.km c in
  write_at_end k.log (plain, (c, t));
  let h = FStar.HyperStack.ST.get () in
  assert (EtM.CPA.invariant (Key?.ke k) h);
  admit();
  (c, t)

val decrypt: k:key -> c:cipher -> ST (option Plain.plain)
  (requires (fun h0 -> invariant h0 k))
  (ensures (fun h0 res h1 ->
    modifies_none h0 h1 /\
    invariant h1 k /\
    (b2t Ideal.uf_cma /\ Some? res ==>
     Seq.mem (Some?.v res, c) (get_log h0 k))))
let decrypt k (c,tag) =
  if MAC.verify k.km c tag
  then let msg = CPA.decrypt k.ke c in
       Some msg
  else None
