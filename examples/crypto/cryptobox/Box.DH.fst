(**
   TODO: - Documentation, some cleanup.
	 - make decrypt a total function.
*)
module Box.DH

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.List.Tot

open CoreCrypto
open Platform.Bytes

open Box.Indexing
open Box.PlainDH
open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HS = FStar.HyperStack
module HH = FStar.HyperHeap


assume val dh_element_size : nat
assume val dh_exponent_size : nat
type dh_element =lbytes dh_element_size
type dh_share = dh_element
assume val dh_base : dh_element
abstract type dh_exponent = lbytes dh_exponent_size

assume val dh_gen_key: unit -> ST (dh_share*dh_exponent)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0==h1
  ))

type keysize = aeadKeySize AES_128_GCM
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)
assume val hash: dh_element -> Tot aes_key

(*
  Setting up a global log for AE.keys indexed by the ids of the public and private key involved.
*)
private type dh_key_log_range = fun (k_id:id{AE_id? k_id}) -> k:PlainDH.key{PlainDH.ae_key_get_index k = k_id}

(**
   Invariant for the dh_key_log: If a key is honest and we idealize prf_odh, then if it is unfresh,
   there has to be an entry in the dh_key_log.
*)
private let dh_key_log_inv (m:MM.map' (i:id{AE_id? i}) dh_key_log_range) = True
//  forall (i:id{AE_id? i}). (honest i /\ prf_odh) ==> (Some? (MM.sel m i) ==> unfresh i)


assume val dh_key_log_region: (r:HH.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r ae_key_region
					 /\ disjoint r id_freshness_table_region
					 /\ disjoint r id_honesty_table_region
					 })
assume val dh_key_log: MM.t dh_key_log_region (i:id{AE_id? i}) dh_key_log_range dh_key_log_inv

noeq abstract type dh_pkey = 
  | DH_pkey: #pk_id:id{DH_id? pk_id /\ unfresh pk_id /\ registered pk_id} -> rawpk:dh_share -> dh_pkey

noeq abstract type dh_skey =
  | DH_skey: #sk_id:id{DH_id? sk_id /\ unfresh sk_id /\ registered sk_id} -> rawsk:dh_exponent -> pk:dh_pkey{pk.pk_id=sk_id} -> dh_skey 

val sk_get_index: sk:dh_skey -> Tot (i:id{i = sk.sk_id})
let sk_get_index k = k.sk_id

val pk_get_index: pk:dh_pkey -> Tot (i:id{i = pk.pk_id})
let pk_get_index k = k.pk_id

val pk_get_rawpk: pk:dh_pkey -> Tot (raw:dh_share{raw=pk.rawpk})
let pk_get_rawpk pk =
  pk.rawpk

assume val dh_exponentiate: dh_element -> dh_exponent -> Tot dh_element

val keygen: #i:id{DH_id? i} -> ST (dh_pair:(k:dh_pkey{k.pk_id=i}) * (k:dh_skey{k.sk_id=i}))
  (requires (fun h -> 
    fresh i h
    /\ registered i
  ))
  (ensures (fun h0 k h1 -> 
    unfresh i
    /\ modifies (Set.singleton id_freshness_table_region) h0 h1
  ))
let keygen #i =
  make_unfresh i;
  let dh_share,dh_exponent = dh_gen_key() in
  let dh_pk = DH_pkey #i dh_share in
  let dh_sk = DH_skey #i dh_exponent dh_pk in
  dh_pk,dh_sk

val coerce_pkey: #i:id{DH_id? i /\ dishonest i} -> dh_share -> ST (pk:dh_pkey{pk.pk_id=i})
  (requires (fun h0 -> 
    fresh i h0
    /\ registered i
  ))
  (ensures (fun h0 pk h1 -> 
    unfresh i
  ))
let coerce_pkey #i dh_sh =
  make_unfresh i;
  DH_pkey #i dh_sh

val coerce_keypair: #i:id{DH_id? i /\ dishonest i} -> dh_exponent -> ST (dh_pair:(k:dh_pkey{k.pk_id=i}) * (k:dh_skey{k.sk_id=i}))
  (requires (fun h0 -> 
    fresh i h0
    /\ registered i
  ))
  (ensures (fun h0 pk h1 -> 
    unfresh i
  ))
let coerce_keypair #i dh_ex =
  make_unfresh i;
  let dh_sh = dh_exponentiate dh_base dh_ex in
  let pk = DH_pkey #i dh_sh in
  let sk = DH_skey #i dh_ex pk in
  pk,sk


// Make this function GTot
val prf_odhT: dh_skey -> dh_pkey -> GTot aes_key
let prf_odhT dh_sk dh_pk =
  let pk_id = dh_pk.pk_id in
  let sk_id = dh_sk.sk_id in
  let i = generate_ae_id pk_id sk_id in
  let raw_k = dh_exponentiate dh_pk.rawpk dh_sk.rawsk in
  let k = hash raw_k in
  k

#set-options "--z3rlimit 25"
val prf_odh: sk:dh_skey -> pk:dh_pkey -> ST (PlainDH.key)
  ( requires (fun h0 -> 
    let i = generate_ae_id pk.pk_id sk.sk_id in
    (AE_id? i /\ honest i) ==> (MM.defined dh_key_log i h0 \/ fresh i h0)
  ))
  ( ensures (fun h0 k h1 ->
    let i = generate_ae_id pk.pk_id sk.sk_id in
    let regions_modified_dishonest:Set.set (r:HH.rid) = (Set.singleton id_freshness_table_region) in
    let regions_modified_honest = Set.union regions_modified_dishonest (Set.singleton dh_key_log_region) in
    let k_log = get_logGT k in
    (PlainDH.ae_key_get_index k = i)
    /\ MR.m_contains k_log h1
    /\ (fresh i h0 ==> (MR.m_sel h1 (PlainDH.get_logGT k) == PlainDH.empty_log i))
    /\ (honest i ==> (let current_log = MR.m_sel h0 dh_key_log in
		   MR.witnessed (MM.contains dh_key_log i k)
		   /\ (MM.fresh dh_key_log i h0 ==> (MR.m_sel h1 dh_key_log == MM.upd current_log i k
						  /\ MR.m_sel h1 k_log == PlainDH.empty_log i))
		   /\ (MM.defined dh_key_log i h0 ==> (MR.m_sel h0 dh_key_log == MR.m_sel h1 dh_key_log
						    /\ MR.m_sel h0 k_log == MR.m_sel h1 k_log))
		   /\ modifies regions_modified_honest h0 h1
		  )
      )
    /\ (dishonest i
    	==> (modifies regions_modified_dishonest h0 h1
    	   /\ leak_key k = prf_odhT sk pk
    	  )
      )
  ))
let prf_odh dh_sk dh_pk =
  let i = generate_ae_id dh_pk.pk_id dh_sk.sk_id in
  let honest_i = is_honest i in
  MR.m_recall dh_key_log;
  if honest_i then (
    lemma_honest_not_dishonest i;
    MR.m_recall dh_key_log;
    match MM.lookup dh_key_log i with
    | Some  k' ->
	recall_log k'; 
	fresh_unfresh_contradiction i;
        k'
    | None ->
        let k' = PlainDH.keygen i in
        MM.extend dh_key_log i k';
	fresh_unfresh_contradiction i;
        k'
  ) else (
    lemma_dishonest_not_honest i;
    let raw_k = dh_exponentiate dh_pk.rawpk dh_sk.rawsk in
    let hashed_raw_k = hash raw_k in
    let k=PlainDH.coerce_key i hashed_raw_k in
    fresh_unfresh_contradiction i;
    k)

#reset-options
