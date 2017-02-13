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

open Box.Indexing
open Box.PlainDH
open Box.Flags

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
assume val hash: dh_element -> Tot aes_key

(*
  Setting up a global log for AE.keys indexed by the ids of the public and private key involved.
*)
private type range = fun (k_id:ae_id) -> k:PlainDH.key{PlainDH.ae_key_get_index k = k_id}
private let inv (f:MM.map' (ae_id) range) = True

assume val ae_key_log_region: (r:MR.rid{ extends r root /\ is_eternal_region r /\ is_below r root})
//private let ae_key_log_region = new_region root
assume val ae_key_log: MM.t ae_key_log_region ae_id range inv
//private let ae_key_log = MM.alloc #ae_key_log_region #ae_id #range #inv

noeq abstract type dh_pkey = 
  | DH_pkey:  #pk_id:id -> rawpk:dh_share -> dh_pkey

noeq abstract type dh_skey =
  | DH_skey: #sk_id:id -> rawsk:dh_exponent -> pk:dh_pkey{pk.pk_id=sk_id} -> dh_skey 

val sk_get_index: sk:dh_skey -> Tot (i:id{i = sk.sk_id})
let sk_get_index k = k.sk_id

val pk_get_index: pk:dh_pkey -> Tot (i:id{i = pk.pk_id})
let pk_get_index k = k.pk_id

val pk_get_rawpk: pk:dh_pkey -> Tot (raw:dh_share{raw=pk.rawpk})
let pk_get_rawpk pk =
  pk.rawpk

assume val dh_exponentiate: dh_element -> dh_exponent -> Tot dh_element

val keygen: #i:id -> ST (dh_pair:(k:dh_pkey{k.pk_id=i}) * (k:dh_skey{k.sk_id=i}))
  (requires (fun h -> True))
  (ensures (fun h0 k h1 -> True))
let keygen #i =
  let dh_share,dh_exponent = dh_gen_key() in
  let dh_pk = DH_pkey #i dh_share in
  let dh_sk = DH_skey #i dh_exponent dh_pk in
  dh_pk,dh_sk

val coerce_pkey: #i:id{dishonest i} -> dh_share -> St (pk:dh_pkey{pk.pk_id=i})
let coerce_pkey #i dh_sh =
  DH_pkey #i dh_sh

val coerce_keypair: #i:id{dishonest i} -> dh_exponent -> St (dh_pair:(k:dh_pkey{k.pk_id=i}) * (k:dh_skey{k.sk_id=i}))
let coerce_keypair #i dh_ex =
  let dh_sh = dh_exponentiate dh_base dh_ex in
  let pk = DH_pkey #i dh_sh in
  let sk = DH_skey #i dh_ex pk in
  pk,sk


val prf_odhT: dh_skey -> dh_pkey -> Tot aes_key
let prf_odhT dh_sk dh_pk =
  let pk_id = dh_pk.pk_id in
  let sk_id = dh_sk.sk_id in
  let i = generate_ae_id pk_id sk_id in
  let raw_k = dh_exponentiate dh_pk.rawpk dh_sk.rawsk in
  let k = hash raw_k in
  k
  

(**
   If we prf_odh is true, the output of this function is random, if both 
   share and exponent are honest.
*)
val prf_odh: sk:dh_skey -> pk:dh_pkey -> ST (PlainDH.key)
  ( requires (fun h0 ->
    let i = generate_ae_id pk.pk_id sk.sk_id in
    ae_fixed i
    /\ (ae_honest i \/ ae_dishonest i)
  ))
  ( ensures (fun h0 k h1 ->
    let i = generate_ae_id pk.pk_id sk.sk_id in
    (PlainDH.ae_key_get_index k = i)
    /\ (ae_honest i \/ ae_dishonest i)
    /\ (
        ( (ae_honest i /\ prf_odh)
	    ==> (
	       MR.witnessed (MM.contains ae_key_log i k) 
	      )
        )
        \/ 
	( (ae_dishonest i \/ ~prf_odh)
	    ==> (modifies_none h0 h1
	       /\ leak_key k = prf_odhT sk pk
	      )
        )
      )
  ))
let prf_odh dh_sk dh_pk =
  let pk_id = dh_pk.pk_id in
  let sk_id = dh_sk.sk_id in
  let i = generate_ae_id pk_id sk_id in
  let ae_honest_i = ae_honestST i in
  if ae_honest_i && prf_odh then
    (MR.m_recall ae_key_log;
    let entry = MM.lookup ae_key_log i in
    match entry with
    | Some  k' -> k'
    | None -> 
      let k' = PlainDH.keygen i in
      MM.extend ae_key_log i k';
      k')
  else(
    assert(ae_dishonest i \/ ~prf_odh);
    let raw_k = dh_exponentiate dh_pk.rawpk dh_sk.rawsk in
    let hashed_raw_k = hash raw_k in
    let k=PlainDH.coerce_key i hashed_raw_k in
    k)
