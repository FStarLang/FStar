module Box.PKAE

open Platform.Bytes
open FStar.HyperHeap
open FStar.HyperStack
open Box.Flags
open Box.AE
open Box.DH
open Box.PlainPKAE
open Box.PlainAE
open Box.PlainDH
open Box.Indexing
open CoreCrypto

module B = Platform.Bytes
module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

type rid = FStar.Monotonic.Seq.rid

assume val box_log_region: (r:MR.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r ae_key_region 
					 /\ disjoint r dh_key_log_region
					 /\ disjoint r id_honesty_table_region
					 /\ disjoint r id_freshness_table_region
					 })

assume val box_key_log_region: (r:MR.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r ae_key_region 
					 /\ disjoint r dh_key_log_region
					 /\ disjoint r id_honesty_table_region
					 /\ disjoint r id_freshness_table_region
					 /\ disjoint r box_log_region
					 })
					 
//let pkae_table_region = new_region root


type box_log_key = (nonce*(i:id{AE_id? i /\ honest i}))
type box_log_value = (protected_pkae_plain)
type box_log_range = fun box_log_key -> box_log_value
type box_log_inv (f:MM.map' box_log_key box_log_range) = True
assume val box_log: MM.t box_log_region box_log_key box_log_range box_log_inv
//let box_log = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv

type box_key_log_key = i:id{AE_id? i /\ honest i}
type box_key_log_value = (AE.key)
type box_key_log_range = fun (i:box_key_log_key) -> (k:box_key_log_value{AE.get_index k = i})
type box_key_log_inv (f:MM.map' box_key_log_key box_key_log_range) = True
assume val box_key_log:  MM.t box_key_log_region box_key_log_key box_key_log_range box_key_log_inv
//let box_key_log = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv


noeq abstract type pkae_pkey (pk_id:id{DH_id? pk_id}) =
  | PKey: dh_pk:dh_pkey{DH.pk_get_index dh_pk=pk_id} -> pkae_pkey pk_id

noeq abstract type pkae_skey (sk_id:id{DH_id? sk_id}) =
  | SKey: dh_sk:dh_skey{DH.sk_get_index dh_sk=sk_id} -> pkae_pk:pkae_pkey sk_id -> pkae_skey sk_id

val keygen: #(i:id{DH_id? i}) -> ST (pkae_pkey i * pkae_skey i)
  (requires (fun h0 -> 
  fresh i h0
  /\ registered i
  ))
  (ensures (fun h0 res h1 -> 
    unfresh i
    /\ modifies (Set.singleton id_freshness_table_region) h0 h1
  ))
let keygen #i =
  let (dh_pk, dh_sk) = DH.keygen #i in
  let pkae_pk = PKey #i dh_pk in
  pkae_pk, SKey #i dh_sk pkae_pk


type c = AE.cipher

// TODO: We should be able to replace "dishonest i"  with "~(honest i)" everywhere!
// TODO: Add patterns to quantifiers.
let log_invariant_all_keys (h:mem) = 
  // Removed this and made it a requirement only for the id that is currently handled.
  //(forall (i:id{AE_id? i /\ honest i}) . MM.defined box_key_log i h <==> MM.defined dh_key_log i h) // dh_key_log and box_key_log are in sync
  // Removed this and made it a requirement only for the id that is currently handled.
  ///\ (forall (i:id{AE_id? i /\ honest i}) . MM.fresh box_key_log i h <==> fresh i h) // all honest keys must be present in the box_key_log
  (forall (i:id{AE_id? i /\ honest i}) (n:nonce) . (MM.defined box_key_log i h ==> (let k = MM.value box_key_log i h in // if it is in the box_key_log, then box_log and the local key_log
  									    let k_log = get_logGT k in          // should be in sync.
  									    (MM.defined box_log (n,i) h <==> MM.defined k_log n h))))
  /\ (forall (i:id{AE_id? i /\ honest i}) . (MM.defined box_key_log i h ==> (let k = MM.value box_key_log i h in // if it is in the box_key_log, then box_log and the local key_log
  									    let k_log = get_logGT k in          // should be in sync.
									    MR.m_contains k_log h)))
  // Removed this and made it a requirement only for the id that is currently handled.
  ///\ (forall (i:id{AE_id? i /\ honest i}) (n:nonce) . (MM.fresh box_key_log i h ==> MM.fresh box_log (n,i) h)) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log

let log_invariant_id (h:mem) (i:id) =
  ((AE_id? i /\ honest i) ==> (MM.fresh box_key_log i h <==> fresh i h)) // If the id is honest and unfresh, then it must be in the key_log.
  /\ ((AE_id? i /\ honest i) ==> (MM.defined box_key_log i h <==> MM.defined dh_key_log i h)) // dh_key_log and box_key_log are in sync
  /\ (forall (n:nonce) . (AE_id? i /\ honest i /\ (b2t pkae)) ==> (MM.fresh box_key_log i h ==> MM.fresh box_log (n,i) h)) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log

let log_invariant_single_key (h:mem) (i:id) (k:AE.key) =
  ((AE_id? i /\ honest i /\ (b2t pkae)) ==> (forall (n:nonce) . (MM.defined box_key_log i h ==> (let k_log = get_logGT k in
  								      (MM.defined box_log (n,i) h <==> MM.defined k_log n h)))))
  /\ (AE_id? i /\ honest i /\ (b2t pkae) /\ MM.defined box_key_log i h ==> (let k_log = get_logGT k in MR.m_contains k_log h))

val recall_global_logs: unit -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> 
    h0 == h1
    /\ MR.m_contains id_freshness_table h1
    /\ MR.m_contains box_log h1
    /\ MR.m_contains box_key_log h1
    /\ MR.m_contains dh_key_log h1
  ))
let recall_global_logs () =
  MR.m_recall id_freshness_table;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  MR.m_recall box_key_log


#set-options "--z3rlimit 30"
val box_beforenm: #(pk_id:id{DH_id? pk_id /\ registered pk_id}) -> 
	              #(sk_id:id{DH_id? sk_id /\ registered sk_id}) -> 
	              pk:pkae_pkey pk_id -> 
	              sk:pkae_skey sk_id ->
		      ST (k:AE.key)
  (requires (fun h0 -> 
    let i = generate_ae_id pk_id sk_id in
    registered i
    /\ log_invariant_all_keys h0
    /\ log_invariant_id h0 i
    /\ MR.m_contains id_freshness_table h0
    /\ MR.m_contains box_log h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
  ))
  (ensures (fun h0 k h1 -> 
    let i = generate_ae_id pk_id sk_id in
    let regions_modified_dishonest = [id_freshness_table_region] in
    let regions_modified_honest_set = Set.as_set (regions_modified_dishonest @ [dh_key_log_region;box_key_log_region]) in
    let regions_modified_dishonest_set:Set.set (r:HH.rid) = Set.as_set regions_modified_dishonest in
    let k_log = get_logGT k in
    (AE.get_index k = generate_ae_id pk_id sk_id)
    /\ (honest i
      ==> (modifies regions_modified_honest_set h0 h1
    	 /\ MR.witnessed (MM.contains box_key_log i k))
	 /\ MM.contains box_key_log i k h1)
    /\ (dishonest i
      ==> (modifies regions_modified_dishonest_set h0 h1
         /\ leak_key k = DH.prf_odhT sk.dh_sk pk.dh_pk))
    /\ MR.m_contains k_log h1
    /\ modifies regions_modified_honest_set h0 h1
    /\ log_invariant_single_key h1 i k
    /\ log_invariant_id h1 i
    /\ MR.m_contains id_freshness_table h1
    /\ MR.m_contains box_log h1
    /\ MR.m_contains box_key_log h1
    /\ MR.m_contains dh_key_log h1
    // Would like to ensure for all keys, but verification takes too much time. Need a smarter invariant (via patterns?).
    ///\ log_invariant_all_keys h1
  ))
let box_beforenm #pk_id #sk_id pk sk =
  let i = generate_ae_id pk_id sk_id in
  if is_honest i then
    match MM.lookup box_key_log i with
    | Some k -> 
	recall_global_logs();
	recall_log k;
        k
    | None ->
        let k = prf_odh sk.dh_sk pk.dh_pk in
        MM.extend box_key_log i k;
	recall_global_logs();
	recall_log k;
        k
  else (
    let k = prf_odh sk.dh_sk pk.dh_pk in
    recall_global_logs();
    recall_log k;
    k)


val box_afternm: k:AE.key ->
		     n:nonce ->
		     p:protected_pkae_plain{PlainPKAE.get_index p = AE.get_index k} ->
		     ST c
  (requires (fun h0 -> 
    let k_log = get_logGT k in
    let i = AE.get_index k in
    MR.m_contains k_log h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains box_log h0
    /\ log_invariant_single_key h0 i k
    /\ log_invariant_id h0 i
    /\ ((honest i /\ b2t pkae) ==> MM.fresh box_log (n,i) h0)
    /\ ((honest i) ==> MM.defined box_key_log i h0)
  ))
  (ensures (fun h0 c h1 -> 
    let i = AE.get_index k in
    let k_log = get_logGT k in
    let k_raw = get_keyGT k in
    ((dishonest i \/ ~(b2t ae_ind_cca))
      ==> c = CoreCrypto.aead_encryptT AES_128_CCM k_raw n empty_bytes (PlainPKAE.repr p))
    /\ ((honest i /\ b2t ae_ind_cca)
      ==> c = CoreCrypto.aead_encryptT AES_128_CCM k_raw n empty_bytes (createBytes (PlainPKAE.length p) 0z)
	/\ MR.witnessed (MM.contains k_log n (c,ae_message_wrap p))
	/\ MR.witnessed (MM.contains box_log (n,i) p))
    /\ log_invariant_single_key h1 i k
    /\ log_invariant_id h1 i
  ))
let box_afternm k n p =
  MR.m_recall box_key_log;
  MR.m_recall id_freshness_table;
  MR.m_recall dh_key_log;
  let i = AE.get_index k in
  let ae_m = ae_message_wrap #i p in
  let honest_i = is_honest i in
  if honest_i && pkae then (
    MM.extend box_log (n,i) p;
    let c = AE.encrypt #i n k ae_m in
    c
  ) else (
    let c = AE.encrypt #i n k ae_m in
    c)
  

#set-options "--z3rlimit 25"
val box: #(pk_id:id{DH_id? pk_id}) -> 
	     #(sk_id:id{DH_id? sk_id}) -> 
	     pk:pkae_pkey pk_id{registered pk_id} -> 
	     sk:pkae_skey sk_id{registered sk_id} -> 
	     n:nonce -> 
	     p:protected_pkae_plain{PlainPKAE.get_index p = generate_ae_id pk_id sk_id} 
	     -> ST c
  (requires (fun h0 ->
    let i = generate_ae_id pk_id sk_id in
    registered i
    // Liveness of global logs
    /\ MR.m_contains box_log h0
    /\ MR.m_contains id_freshness_table h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
    // Make sure that log_invariants hold.
    /\ log_invariant_all_keys h0
    /\ log_invariant_id h0 i
    // Make sure that nonce is fresh
    /\ ((honest i /\ b2t pkae) ==> MM.fresh box_log (n,i) h0)
  ))
  (ensures (fun h0 c h1 -> 
    let i = generate_ae_id pk_id sk_id in
    // Make sure that log_invariants hold. Would like to ensure "all_keys" variant, but too expensive to verify currently.
    log_invariant_id h1 i
    ///\ log_invariant_all_keys h1
  ))
let box #pk_id #sk_id pkae_pk pkae_sk n p =
  let k = box_beforenm #pk_id #sk_id pkae_pk pkae_sk in
  let c = box_afternm k n p in
  c


val box_open: #(sk_id:id{DH_id? sk_id}) -> 
	     #(pk_id:id{DH_id? pk_id}) -> 
	     n:nonce ->  
	     sk:pkae_skey sk_id{registered sk_id} -> 
	     pk:pkae_pkey pk_id{registered pk_id} -> 
	     c:cipher{B.length c >= aeadTagSize AES_128_CCM} ->
	     ST(option (p:protected_pkae_plain{PlainPKAE.get_index p = generate_ae_id pk_id sk_id}))
  (requires (fun h0 ->
    let i = generate_ae_id pk_id sk_id in
    registered i
    // Liveness of global logs
    /\ MR.m_contains box_log h0
    /\ MR.m_contains id_freshness_table h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
    // Make sure that log_invariants hold.
    /\ log_invariant_all_keys h0
    /\ log_invariant_id h0 i
    // Make sure that nonce is fresh
  ))
  (ensures (fun h0 p h1 -> 
    let i = generate_ae_id pk_id sk_id in
    // Make sure that log_invariants hold. Would like to ensure "all_keys" variant, but too expensive to verify currently.
    log_invariant_id h1 i
    ///\ log_invariant_all_keys h1
  ))
let box_open #sk_id #pk_id n sk pk c =
  let k = box_beforenm #pk_id #sk_id pk sk in
  let i = AE.get_index k in
  match AE.decrypt #i n k c with
  | Some p -> 
    let p' = (PlainAE.ae_message_unwrap #i p) in 
    Some p'
  | None -> None
