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

assume val pkae_afternm_table_region: (r:MR.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r ae_key_region 
					 /\ disjoint r dh_key_log_region
					 /\ disjoint r id_honesty_table_region
					 /\ disjoint r id_freshness_table_region
					 })

assume val pkae_beforenm_table_region: (r:MR.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r ae_key_region 
					 /\ disjoint r dh_key_log_region
					 /\ disjoint r id_honesty_table_region
					 /\ disjoint r id_freshness_table_region
					 /\ disjoint r pkae_afternm_table_region
					 })
					 
//let pkae_table_region = new_region root


type pkae_afternm_table_key = (nonce*(i:id{AE_id? i}))
type pkae_afternm_table_value = (protected_pkae_plain)
type pkae_afternm_table_range = fun pkae_afternm_table_key -> pkae_afternm_table_value
type pkae_afternm_table_inv (f:MM.map' pkae_afternm_table_key pkae_afternm_table_range) = True
assume val pkae_afternm_table: MM.t pkae_afternm_table_region pkae_afternm_table_key pkae_afternm_table_range pkae_afternm_table_inv
//let pkae_afternm_table = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv

type pkae_beforenm_table_key = i:id{AE_id? i}
type pkae_beforenm_table_value = (AE.key)
type pkae_beforenm_table_range = fun (i:pkae_beforenm_table_key) -> (k:pkae_beforenm_table_value{AE.get_index k = i})
type pkae_beforenm_table_inv (f:MM.map' pkae_beforenm_table_key pkae_beforenm_table_range) = True
assume val pkae_beforenm_table:  MM.t pkae_beforenm_table_region pkae_beforenm_table_key pkae_beforenm_table_range pkae_beforenm_table_inv
//let pkae_beforenm_table = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv


noeq abstract type pkae_pkey (pk_id:id{DH_id? pk_id}) =
  | PKey: dh_pk:dh_pkey{DH.pk_get_index dh_pk=pk_id} -> pkae_pkey pk_id

noeq abstract type pkae_skey (sk_id:id{DH_id? sk_id}) =
  | SKey: dh_sk:dh_skey{DH.sk_get_index dh_sk=sk_id} -> pkae_pk:pkae_pkey sk_id -> pkae_skey sk_id

val keygen: #(i:id{DH_id? i}) -> ST (pkae_pkey i * pkae_skey i)
  (requires (fun h0 -> 
  fresh i h0
  /\ fixed i
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

let log_invariant (h:mem) = 
  forall (k:AE.key) (n:nonce). let k_log = get_logGT k in (MM.fresh k_log n h <==> MM.fresh pkae_afternm_table (n,AE.get_index k) h)

#set-options "--z3rlimit 15"
val encrypt_beforenm: #(pk_id:id{DH_id? pk_id /\ fixed pk_id}) -> 
	              #(sk_id:id{DH_id? sk_id /\ fixed sk_id}) -> 
	              pk:pkae_pkey pk_id -> 
	              sk:pkae_skey sk_id ->
		      ST (k:AE.key)
  (requires (fun h0 -> 
    let i = generate_ae_id pk_id sk_id in
    fixed i
    /\ honest i ==> (~(MR.witnessed(MM.defined dh_key_log i) ==> ~(fresh i h0)))
    /\ log_invariant h0
  ))
  (ensures (fun h0 k h1 -> 
    let i = generate_ae_id pk_id sk_id in
    let regions_modified_dishonest:Set.set (r:HH.rid) = (Set.singleton id_freshness_table_region) in
    let regions_modified_honest = Set.union regions_modified_dishonest (Set.singleton dh_key_log_region) in
    let k_log = get_logGT k in
    (PlainDH.ae_key_get_index k = i)
    /\ (
        ( (honest i)
    	    ==> (modifies regions_modified_honest h0 h1
    	       /\ MR.witnessed (MM.contains dh_key_log i k) 
    	      )
        )
        \/ 
    	( (dishonest i \/ ~Flags.prf_odh)
    	    ==> (modifies regions_modified_dishonest h0 h1
    	       /\ leak_key k = DH.prf_odhT sk.dh_sk pk.dh_pk
    	      )
        )
      )
    /\ MR.m_contains k_log h1
    /\ modifies regions_modified_honest h0 h1
    /\ (forall k. let k_region = get_regionGT k in
      equal_on (Set.singleton k_region) h0.h h1.h)
    /\ (let k_region = get_regionGT k in
      equal_on (Set.singleton pkae_afternm_table_region) h0.h h1.h)
    /\ log_invariant h1
  ))
let encrypt_beforenm #pk_id #sk_id pk sk =
  MR.m_recall pkae_afternm_table;
  let k = prf_odh sk.dh_sk pk.dh_pk in
  recall_log k;
  k


// Implement invariant that states equality of logs before and after encrypt_afternm.
//   - quantify over all nonces and prove that lookups on both logs result in the same values.
val encrypt_afternm: k:AE.key ->
		     n:nonce ->
		     p:protected_pkae_plain{PlainPKAE.get_index p = AE.get_index k} ->
		     ST c
  (requires (fun h0 -> 
    let k_log = get_logGT k in
    MM.fresh pkae_afternm_table (n,AE.get_index k) h0
    /\ MR.m_contains k_log h0
    /\ MR.m_contains pkae_afternm_table h0
    /\ log_invariant h0
  ))
  (ensures (fun h0 c h1 -> 
    let i = AE.get_index k in
    let k_log = get_logGT k in
    let k_raw = get_keyGT k in
    ///\ (
    //	( (dishonest i \/ ~(b2t pkae))
    //	    ==> c = CoreCrypto.aead_encryptT AES_128_CCM k_raw n empty_bytes (PlainPKAE.repr p))
    //  \/ 
    //    ( (honest i /\ b2t ae_ind_cca)
    //	    ==> c = CoreCrypto.aead_encryptT AES_128_CCM k_raw n empty_bytes (createBytes (PlainPKAE.length p) 0z) )
    //  )
    (dishonest i \/ honest i)
    /\ MR.witnessed (MM.contains k_log n (c,ae_message_wrap p))
    /\ MR.witnessed (MM.contains pkae_afternm_table (n,i) p)
    /\ log_invariant h0
  ))
let encrypt_afternm k n p =
//  let h0 = ST.get() in
//  assert(
//    let k_log = get_logGT k in
//    MM.fresh k_log n h0);
//  admit();
  let ae_i = AE.get_index k in
  let ae_m = ae_message_wrap #ae_i p in
  MM.extend pkae_afternm_table (n,ae_i) p;
  AE.encrypt #ae_i n k ae_m
  

#set-options "--z3rlimit 15"
val encrypt: #(pk_id:id{DH_id? pk_id}) -> 
	     #(sk_id:id{DH_id? sk_id}) -> 
	     pk:pkae_pkey pk_id{fixed pk_id} -> 
	     sk:pkae_skey sk_id{fixed sk_id} -> 
	     n:nonce -> 
	     p:protected_pkae_plain{PlainPKAE.get_index p = generate_ae_id pk_id sk_id} 
	     -> ST c 
  (requires (fun h0 ->
    let i = generate_ae_id pk_id sk_id in
    fixed i
    /\ MR.m_contains pkae_afternm_table h0
    /\ (honest i ==> (~(MR.witnessed(MM.defined dh_key_log i) ==> ~(fresh i h0))))
    /\ MM.fresh pkae_afternm_table (n,i) h0
    // Make sure that log_invariant holds
    /\ MM.fresh pkae_afternm_table (n,i) h0
    /\ log_invariant h0
  ))
  (ensures (fun h0 c h1 -> 
    log_invariant h1
  ))
let encrypt #pk_id #sk_id pkae_pk pkae_sk n p =
  let k = encrypt_beforenm #pk_id #sk_id pkae_pk pkae_sk in
  let c = encrypt_afternm k n p in
  c


// Implement decrypt_beforenm and decrypt_afternm
// - add similar specification as in AE and in PKAE.encrypt..
val decrypt: #(sk_id:id) -> 
	     #(pk_id:id) -> 
	     n:nonce ->  
	     pkae_skey sk_id -> 
	     pkae_pkey sk_id -> 
	     c -> 
	     St(option (p:protected_pkae_plain))
	     
let decrypt #sk_id #pk_id n sk pk c =
  MR.m_recall pkae_afternm_table;
  let (dh_sh,ae_c) = c in 
  let k = prf_odh sk.dh_sk pk.dh_pk  in
  let ae_i = AE.get_index k in
  match AE.decrypt #ae_i n k ae_c with
  | Some p -> 
    let p' = (PlainAE.ae_message_unwrap #ae_i p) in 
    Some p'
  | None -> None
