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
let log_invariant (h:mem) = 
  (forall (i:id{AE_id? i /\ honest i}) . MM.defined box_key_log i h <==> MM.defined dh_key_log i h) // dh_key_log and box_key_log are in sync
  /\ 
  (forall (i:id{AE_id? i /\ honest i}) . MM.fresh box_key_log i h <==> fresh i h) // all honest keys must be present in the box_key_log
  /\
  (forall (i:id{AE_id? i /\ honest i}) (n:nonce) . (MM.defined box_key_log i h ==> (let k = MM.value box_key_log i h in // if it is in the box_key_log, then box_log and the local key_log
  									    let k_log = get_logGT k in          // should be in sync.
  									    (MM.defined box_log (n,i) h <==> MM.defined k_log n h))))
  /\
  (forall (i:id{AE_id? i /\ honest i}) . (MM.defined box_key_log i h ==> (let k = MM.value box_key_log i h in // if it is in the box_key_log, then box_log and the local key_log
  									    let k_log = get_logGT k in          // should be in sync.
									    MR.m_contains k_log h)))

  /\ (forall (i:id{AE_id? i /\ honest i}) (n:nonce) . (MM.fresh box_key_log i h ==> MM.fresh box_log (n,i) h)) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log


#set-options "--z3rlimit 25"
val encrypt_beforenm: #(pk_id:id{DH_id? pk_id /\ registered pk_id}) -> 
	              #(sk_id:id{DH_id? sk_id /\ registered sk_id}) -> 
	              pk:pkae_pkey pk_id -> 
	              sk:pkae_skey sk_id ->
		      ST (k:AE.key)
  (requires (fun h0 -> 
    let i = generate_ae_id pk_id sk_id in
    registered i
    /\ log_invariant h0
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
    ///\ (honest i
    //  ==> (modifies regions_modified_honest_set h0 h1
    //	 /\ MR.witnessed (MM.contains box_key_log i k)))
    ///\ (dishonest i
    //  ==> (modifies regions_modified_dishonest_set h0 h1
    //     /\ leak_key k = DH.prf_odhT sk.dh_sk pk.dh_pk))
    ///\ MR.m_contains k_log h1
    ///\ modifies regions_modified_honest_set h0 h1
    ///\ log_invariant h1
    /\ 
  //(forall (i:id{AE_id? i /\ honest i}) . MM.defined box_key_log i h1 <==> MM.defined dh_key_log i h1) // dh_key_log and box_key_log are in sync
  ///\ 
  (forall (i:id{AE_id? i /\ honest i}) . MM.fresh box_key_log i h1 <==> fresh i h1) // all honest keys must be present in the box_key_log
  /\
  //(forall (i:id{AE_id? i /\ honest i}) (n:nonce) .{:pattern (MM.defined box_log (n,i))} (MM.defined box_key_log i h1 ==> (let k = MM.value box_key_log i h1 in // if it is in the box_key_log, then box_log and the local key_log
  //									    let k_log = get_logGT k in          // should be in sync.
  //									    (MM.defined box_log (n,i) h1 <==> MM.defined k_log n h1))))
  ///\
  (forall (i:id{AE_id? i /\ honest i}) . (MM.defined box_key_log i h1 ==> (let k = MM.value box_key_log i h1 in // if it is in the box_key_log, then box_log and the local key_log
									    let k_log = get_logGT k in          // should be in sync.
									    MR.m_contains k_log h1)))

  ///\ (forall (i:id{AE_id? i /\ honest i}) (n:nonce) . (MM.fresh box_key_log i h1 ==> MM.fresh box_log (n,i) h1)) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log
    // Not sure exactly how we are proving this...
    ///\ (forall (k':AE.key) . ~(k == k') <==> generate_ae_id pk_id sk_id <> AE.get_index k')
  ))
let encrypt_beforenm #pk_id #sk_id pk sk =
  let i = generate_ae_id pk_id sk_id in
  if is_honest i then
    match MM.lookup box_key_log i with
    | Some k -> 
	recall_log k;
        k
    | None ->
        let k = prf_odh sk.dh_sk pk.dh_pk in
        MM.extend box_key_log i k;
	recall_log k;
        k
  else (
    let k = prf_odh sk.dh_sk pk.dh_pk in
    recall_log k;
    k)
//
//
//val encrypt_afternm: k:AE.key ->
//		     n:nonce ->
//		     p:protected_pkae_plain{PlainPKAE.get_index p = AE.get_index k} ->
//		     ST c
//  (requires (fun h0 -> 
//    let k_log = get_logGT k in
//    let i = AE.get_index k in
//    MR.m_contains k_log h0
//    /\ MR.m_contains box_key_log h0
//    /\ MR.m_contains box_log h0
//    /\ log_invariant h0
//    /\ ((honest i /\ b2t pkae) ==> MM.fresh box_log (n,i) h0)
//    /\ ((honest i) ==> MM.defined box_key_log i h0)
//    // We need to prove this somehow.
//    /\ (forall (k':AE.key) . ~(k == k') ==> AE.get_index k' <> i)
//  ))
//  (ensures (fun h0 c h1 -> 
//    let i = AE.get_index k in
//    let k_log = get_logGT k in
//    let k_raw = get_keyGT k in
//    (dishonest i \/ ~(b2t ae_ind_cca))
//      ==> c = CoreCrypto.aead_encryptT AES_128_CCM k_raw n empty_bytes (PlainPKAE.repr p)
//    /\ (honest i /\ b2t ae_ind_cca)
//      ==> c = CoreCrypto.aead_encryptT AES_128_CCM k_raw n empty_bytes (createBytes (PlainPKAE.length p) 0z)
//    /\ MR.witnessed (MM.contains k_log n (c,ae_message_wrap p))
//    /\ MR.witnessed (MM.contains box_log (n,i) p)
//    /\ log_invariant h0
//  ))
//let encrypt_afternm k n p =
//  let i = AE.get_index k in
//  let ae_m = ae_message_wrap #i p in
//  let honest_i = is_honest i in
//  if honest_i && pkae then (
//    let h = ST.get() in
//    MM.extend box_log (n,i) p;
//    AE.encrypt #i n k ae_m
//  ) else (
//    AE.encrypt #i n k ae_m)
//  
//
//#set-options "--z3rlimit 25"
//val encrypt: #(pk_id:id{DH_id? pk_id}) -> 
//	     #(sk_id:id{DH_id? sk_id}) -> 
//	     pk:pkae_pkey pk_id{registered pk_id} -> 
//	     sk:pkae_skey sk_id{registered sk_id} -> 
//	     n:nonce -> 
//	     p:protected_pkae_plain{PlainPKAE.get_index p = generate_ae_id pk_id sk_id} 
//	     -> ST c
//  (requires (fun h0 ->
//    let i = generate_ae_id pk_id sk_id in
//    registered i
//    /\ MR.m_contains box_log h0
//    /\ (honest i ==> MM.fresh box_log (n,i) h0)
//    /\ MR.m_contains id_freshness_table h0
//    /\ MR.m_contains box_log h0
//    // Make sure that log_invariant holds
//    /\ log_invariant h0
//  ))
//  (ensures (fun h0 c h1 -> 
//    log_invariant h1
//  ))
//let encrypt #pk_id #sk_id pkae_pk pkae_sk n p =
//  let k = encrypt_beforenm #pk_id #sk_id pkae_pk pkae_sk in
//  assert(AE.get_index k = generate_ae_id pk_id sk_id);
//  admit();
//  let c = encrypt_afternm k n p in
//  c
//  
//
//// Implement decrypt_beforenm and decrypt_afternm
//// - add similar specification as in AE and in PKAE.encrypt..
//val decrypt: #(sk_id:id) -> 
//	     #(pk_id:id) -> 
//	     n:nonce ->  
//	     pkae_skey sk_id -> 
//	     pkae_pkey sk_id -> 
//	     c -> 
//	     St(option (p:protected_pkae_plain))
//	     
//let decrypt #sk_id #pk_id n sk pk c =
//  MR.m_recall box_log;
//  let (dh_sh,ae_c) = c in 
//  let k = prf_odh sk.dh_sk pk.dh_pk  in
//  let ae_i = AE.get_index k in
//  match AE.decrypt #ae_i n k ae_c with
//  | Some p -> 
//    let p' = (PlainAE.ae_message_unwrap #ae_i p) in 
//    Some p'
//  | None -> None
