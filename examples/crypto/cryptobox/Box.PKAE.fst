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

type rid = FStar.Monotonic.Seq.rid

(**
   Idealisation behaviour of PKAE: 
     - Requires idealization of both DH and AE
     - We maintain a global log, that maps a nonce and an AE.key to a message.
     - When encrypting, we add a new log entry under that nonce AE.key involved.
*)
assume val pkae_table_region: (r:MR.rid)//{ extends r root /\ is_eternal_region r /\ is_below r root /\ disjoint r id_table_region})
//let pkae_table_region = new_region root


type pkae_afternm_table_key = (nonce*ae_id)
type pkae_afternm_table_value = (protected_pkae_plain)
type pkae_afternm_table_range = fun pkae_afternm_table_key -> pkae_afternm_table_value
type pkae_afternm_table_inv (f:MM.map' pkae_afternm_table_key pkae_afternm_table_range) = True
assume val pkae_afternm_table: MM.t pkae_table_region pkae_afternm_table_key pkae_afternm_table_range pkae_afternm_table_inv
//let pkae_afternm_table = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv

type pkae_beforenm_table_key = (ae_id)
type pkae_beforenm_table_value = (AE.key)
type pkae_beforenm_table_range = fun (i:pkae_beforenm_table_key) -> (k:pkae_beforenm_table_value{AE.get_index k = i})
type pkae_beforenm_table_inv (f:MM.map' pkae_beforenm_table_key pkae_beforenm_table_range) = True
assume val pkae_beforenm_table:  MM.t pkae_table_region pkae_beforenm_table_key pkae_beforenm_table_range pkae_beforenm_table_inv
//let pkae_beforenm_table = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv


noeq abstract type pkae_pkey (pk_id:id) =
  | PKey: dh_pk:dh_pkey{DH.pk_get_index dh_pk=pk_id} -> pkae_pkey pk_id

noeq abstract type pkae_skey (sk_id:id) =
  | SKey: dh_sk:dh_skey{DH.sk_get_index dh_sk=sk_id} -> pkae_pk:pkae_pkey sk_id -> pkae_skey sk_id

// Require a fresh id here?
val keygen: #(i:id) -> St (pkae_pkey i * pkae_skey i)
let keygen #i =
  let (dh_pk, dh_sk) = DH.keygen #i in
  let pkae_pk = PKey #i dh_pk in
  pkae_pk, SKey #i dh_sk pkae_pk


type c = AE.cipher

val encrypt_beforenm: #(pk_id:id) -> 
	              #(sk_id:id) -> 
	              pk:pkae_pkey pk_id{fixed pk_id} -> 
	              sk:pkae_skey sk_id{fixed sk_id} ->
		      ST (k:AE.key)
  (requires (fun h0 -> 
    let i = generate_ae_id pk_id sk_id in
    ae_fixed i
    /\ (ae_honest i \/ ae_dishonest i)
  ))
  (ensures (fun h0 k h1 -> 
    let i = generate_ae_id pk_id sk_id in
    AE.get_index k = i
    /\ ((ae_honest i /\ b2t pkae)
      ==> MR.witnessed (MM.contains pkae_beforenm_table i k)
      )
    //\/
    //((ae_dishonest i \/ ~(b2t pkae))
    //  ==> (modifies_none h0 h1
    //	 ///\ leak_key k = prf_odhT sk.dh_sk pk.dh_pk)
    //	)
    //))
    /\ AE.get_index k = generate_ae_id pk_id sk_id
  ))
let encrypt_beforenm #pk_id #sk_id pk sk =
  MR.m_recall pkae_beforenm_table;
  let i = generate_ae_id pk_id sk_id in
  let ae_honest_i = ae_honestST i in
  let k = prf_odh sk.dh_sk pk.dh_pk in
  if ae_honest_i && pkae then
    (assert(ae_honest i /\ b2t pkae);
    match MM.lookup pkae_beforenm_table i with
    | Some k' -> 
      //assert(k==k');
      assert(ae_honest i /\ b2t pkae ==> MR.witnessed (MM.contains pkae_beforenm_table i k'));
      admit();
      k'
    | None ->
      //assert(MM.fresh pkae_beforenm_table i);
      MM.extend pkae_beforenm_table i k;
      assert(ae_honest i /\ b2t pkae ==> MR.witnessed (MM.contains pkae_beforenm_table i k));
      admit();
      k)
  else(
    //assert(ae_honest i /\ b2t pkae); 
    admit();
    k)


// Implement invariant that states equality of logs before and after encrypt_afternm.
//   - quantify over all nonces and prove that lookups on both logs result in the same values.
val encrypt_afternm: k:AE.key ->
		     n:nonce ->
		     p:protected_pkae_plain{PlainPKAE.get_index p = AE.get_index k} ->
		     ST c
  (requires (fun h0 -> 
    MM.fresh pkae_afternm_table (n,AE.get_index k) h0
  ))
  (ensures (fun h0 c h1 -> 
   // Implement GTot function to get the log/raw_key/...
   let i = AE.get_index k in
   let k_log = leak_logGT k in
   let k_raw = leak_keyGT k in
    MR.m_contains k_log h1
    /\ (
	( (ae_dishonest i \/ ~(b2t pkae))
	    ==> c = CoreCrypto.aead_encryptT AES_128_CCM k_raw n empty_bytes (PlainPKAE.repr p))
      \/ 
        ( (ae_honest i /\ b2t ae_ind_cca)
	    ==> c = CoreCrypto.aead_encryptT AES_128_CCM k_raw n empty_bytes (createBytes (PlainPKAE.length #i p) 0z) )
      )
    /\ (ae_dishonest i \/ ae_honest i)
    /\ MR.witnessed (MM.contains k_log n (c,ae_message_wrap p))
    /\ MR.witnessed (MM.contains pkae_afternm_table (n,i) p)
  ))
let encrypt_afternm k n p =
  let ae_i = AE.get_index k in
  let ae_m = ae_message_wrap #ae_i p in
  MM.extend pkae_afternm_table (n,ae_i) p;
  AE.encrypt #ae_i n k ae_m

val encrypt: #(pk_id:id) -> 
	     #(sk_id:id) -> 
	     pk:pkae_pkey pk_id{fixed pk_id} -> 
	     sk:pkae_skey sk_id{fixed sk_id} -> 
	     n:nonce -> 
	     p:protected_pkae_plain{PlainPKAE.get_index p = generate_ae_id pk_id sk_id} 
	     -> ST c 
  (requires (fun h0 -> True ))
  (ensures (fun h0 c h1 -> True ))
let encrypt #pk_id #sk_id pkae_pk pkae_sk n p =
  let k = encrypt_beforenm #pk_id #sk_id pkae_pk pkae_sk in
  let c = encrypt_afternm k n p in
  c


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
  let ae_honest_ae_i = ae_honestST ae_i in
  if pkae && ae_honest_ae_i then
    MM.lookup pkae_afternm_table (n,ae_i)
  else
    (match AE.decrypt #ae_i n k ae_c with
    | Some p -> 
      let p' = (PlainAE.ae_message_unwrap #ae_i p) in 
      Some p'
    | None -> None)
