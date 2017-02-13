(**
   TODO: - Documentation, some cleanup.
	 - make decrypt a total function.
*)
module Box.DH

open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.List.Tot

open CoreCrypto
open Platform.Bytes

//open Box.Indexing
//open Box.PlainDH
open Box.Flags
open Box.KeyScheme

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap


assume val dh_element_size : nat
assume val dh_exponent_size : nat
type dh_element =lbytes dh_element_size
type dh_share = dh_element
assume val dh_base : dh_element
abstract type dh_exponent = lbytes dh_exponent_size
assume val dh_gen_key: unit -> St (dh_share*dh_exponent)

type keysize = aeadKeySize AES_128_GCM
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)
assume val hash: dh_element -> aes_key


noeq abstract type dh_pkey (pk_id_type:eqtype) = 
  | DH_pkey:  #(pk_id:pk_id_type) -> rawpk:dh_share -> dh_pkey pk_id_type


noeq abstract type dh_skey (sk_id_type:eqtype) =
  | DH_skey: #(sk_id:sk_id_type) -> rawsk:dh_exponent -> pk:dh_pkey sk_id_type{pk.pk_id=sk_id} -> dh_skey sk_id_type


val sk_get_index: #id_type:eqtype -> sk:dh_skey id_type -> Tot (i:id_type{i = sk.sk_id})
let sk_get_index #id_type k = k.sk_id


val pk_get_index: #id_type:eqtype -> pk:dh_pkey id_type -> Tot (i:id_type{i = pk.pk_id})
let pk_get_index #id_type k = k.pk_id

val pk_get_rawpk: #id_type:eqtype -> pk:dh_pkey id_type -> Tot (raw:dh_share{raw=pk.rawpk})
let pk_get_rawpk #id_type pk =
  pk.rawpk

assume val dh_exponentiate: dh_element -> dh_exponent -> Tot dh_element

    



//val coerce_pkey: #i:id{dishonest i} -> dh_share -> St (pk:dh_pkey{pk.pk_id=i})
//
//val coerce_keypair: #i:id{dishonest i} -> dh_exponent -> St (dh_pair:(k:dh_pkey{k.pk_id=i}) * (k:dh_skey{k.sk_id=i}))
//
//val prf_odh: ks:key_scheme -> sk:dh_skey -> pk:dh_pkey -> ST (ks.key_type)
//  ( requires (fun _ -> True))
//  ( ensures (fun _ k _ -> True
//    //(ks.get_key_index k = generate_ae_id sk.sk_id pk.pk_id) Re-insert this if we have a good concept of ids
//  ))

noeq type dh_scheme = 
  | DH_scheme: dhs_is:id_scheme ->
	       ks: key_scheme ->
	       ic:id_combiner{  ic.is1 == dhs_is 
                              /\ ic.is2 == ks.ks_is
			      /\ (forall id1 id2. 
			           ic.combine_ids id1 id2 = ic.combine_ids id2 id1)
			     } -> 
	       keygen: (#(i:dhs_is.id_type) -> ST (dh_pair:(k:dh_pkey dhs_is.id_type) * (k:dh_skey dhs_is.id_type))
                 (requires (fun h -> True))
		 (ensures (fun h0 k h1 -> 
		   modifies_none h0 h1
		 ))
	       ) ->
	       coerce_pkey: (#i:dhs_is.id_type{dhs_is.dishonest i} -> dh_share -> Tot (pk:dh_pkey dhs_is.id_type)) ->
	       coerce_keypair: (#i:dhs_is.id_type{dhs_is.dishonest i} -> dh_exponent -> Tot (dh_pair:(k:dh_pkey dhs_is.id_type) * (k:dh_skey dhs_is.id_type))) ->
	       prf_odh: ( sk:dh_skey dhs_is.id_type -> pk:dh_pkey dhs_is.id_type -> ST (ks.key_type)
		 ( requires (fun _ -> 
		   dhs_is.fixed sk.sk_id /\ dhs_is.fixed pk.pk_id))
		 ( ensures (fun _ k _ -> True))
	       ) -> St dh_scheme ks


val dh_spawn_scheme: dhs_is:id_scheme -> 
		     ks:key_scheme -> 
		     ic:id_combiner{  ic.is1 == dhs_is 
				    /\ ic.is2 == ks.ks_is
				    /\ (forall id1 id2. 
				      ic.combine_ids id1 id2 = ic.combine_ids id2 id1)
				   } -> 
		     Tot dh_scheme
let dh_spawn_instance dhs_is ks ic = 
  let ks_key_log_range = fun (k_id:ks.ks_is.id_type) -> k:ks.key_type{k_id = ks.get_key_index k} in
  let ks_key_log_inv (f:MM.map' (ks.ks_is.id_type) ks_key_log_range) = True in
  let ks_key_log = MM.alloc #root #ks.ks_is.id_type #ks_key_log_range #ks_key_log_inv in
  // Maybe give the user the option to choose the region for the log?
  let (ks_key_log_region:MR.rid) = new_region root in
  
  let keygen (#i:dhs_is.id_type) =
    let dh_share,dh_exponent = dh_gen_key() in
    let dh_pk = DH_pkey #dhs_is.id_type #i dh_share in
    let dh_sk = DH_skey #dhs_is.id_type #i dh_exponent dh_pk in
    dh_pk,dh_sk in
  
  let coerce_pkey (#i:dhs_is.id_type{dhs_is.dishonest i}) (dh_sh:dh_share) =
    DH_pkey #dhs_is.id_type #i dh_sh in
  
  let coerce_keypair (#i:dhs_is.id_type{dhs_is.dishonest i}) dh_ex =
    let dh_sh = dh_exponentiate dh_base dh_ex in
    let pk = DH_pkey #dhs_is.id_type #i dh_sh in
    let sk = DH_skey #dhs_is.id_type #i dh_ex pk in
    pk,sk in
  
  let prf_odh (dh_sk:dh_skey dhs_is.id_type) 
	      (dh_pk:dh_pkey dhs_is.id_type) 
	      : ST (ks.key_type)
		 ( requires (fun _ -> 
		   dhs_is.fixed dh_sk.sk_id /\ dhs_is.fixed dh_pk.pk_id))
		 ( ensures (fun h0 k h1 ->
		   let i = ks.get_key_index k in
		   (ks.get_key_index k = ic.combine_ids dh_sk.sk_id dh_pk.pk_id)
		   /\ ( (ks.ks_is.honest i /\ prf_odh)
		       ==> ( MR.witnessed (MM.contains ks_key_log i k) 
			 /\ modifies_one ks_key_log_region h0 h1
			 )
		     )
		   /\ ( (ks.ks_is.dishonest i \/ ~prf_odh)
		       ==> modifies_none h0 h1
		     )

		 ))
	      =
    let pk_id = dh_pk.pk_id in
    let sk_id = dh_sk.sk_id in
    let i = ic.combine_ids sk_id pk_id in
    let honest_i = ks.ks_is.honestST i in
    // Weird bug again??
    assert(False);
    assert(True);
    if honest_i && prf_odh then
      (MR.m_recall ks_key_log;
      let entry = MM.lookup ks_key_log i in
      match entry with
      | Some  k' -> k'
      | None -> 
	let k' = ks.key_gen i in
	MM.extend ks_key_log i k';
	k')
    else
      let raw_k = dh_exponentiate dh_pk.rawpk dh_sk.rawsk in
      let hashed_raw_k = hash raw_k in
      let k=ks.coerce_key i hashed_raw_k in
      k 
  in
	
  DH_scheme dhs_is ks ic keygen coerce_pkey coerce_keypair prf_odh
