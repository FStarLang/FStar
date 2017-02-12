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
val pkae_table_region: (r:MR.rid{ extends r root /\ is_eternal_region r /\ is_below r root})
let pkae_table_region = new_region root


type pkae_table_key = (nonce*ae_id)
type pkae_table_value = (protected_pkae_plain)
type pkae_table_range = fun pkae_table_key -> pkae_table_value
type pkae_table_inv (f:MM.map' pkae_table_key pkae_table_range) = True
let pkae_table = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv


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


type c = DH.dh_share * AE.cipher


val encrypt: #(pk_id:id) -> 
	     #(sk_id:id) -> 
	     pk:pkae_pkey pk_id{fixed pk_id} -> 
	     sk:pkae_skey sk_id{fixed sk_id} -> 
	     n:nonce -> 
	     p:protected_pkae_plain{PlainPKAE.get_index p = generate_ae_id pk_id sk_id} 
	     -> ST c 
  (requires (fun h0 ->
    MM.fresh pkae_table (n,generate_ae_id pk_id sk_id) h0
  ))
  (ensures (fun h0 c h1 ->
    let i = generate_ae_d pk_id sk_id in
    m_contains pkae_table h1
    /\ (
      (ae_dishonest i \/ ~(b2t pkae))
	==> True
      \/
      (ae_honest i /\ (b2t pkae))
	==> 
  ))
  
	     
let encrypt #pk_id #sk_id pkae_pk pkae_sk n p =
  MR.m_recall pkae_table;
  let k = prf_odh pkae_sk.dh_sk pkae_pk.dh_pk in
  let ae_i = AE.get_index k in
  let ae_m = ae_message_wrap #ae_i p in
  MM.extend pkae_table (n,ae_i) p;
  DH.pk_get_rawpk pkae_pk.dh_pk,(AE.encrypt #ae_i n k ae_m)


val decrypt: #(sk_id:id) -> 
	     #(pk_id:id) -> 
	     n:nonce ->  
	     pkae_skey sk_id -> 
	     pkae_pkey sk_id -> 
	     c -> 
	     St(option (p:protected_pkae_plain))
	     
let decrypt #sk_id #pk_id n sk pk c =
  MR.m_recall pkae_table;
  let (dh_sh,ae_c) = c in 
  let k = prf_odh sk.dh_sk pk.dh_pk  in
  let ae_i = AE.get_index k in
  let ae_honest_ae_i = ae_honestST ae_i in
  if pkae && ae_honest_ae_i then
    MM.lookup pkae_table (n,ae_i)
  else
    (match AE.decrypt #ae_i n k ae_c with
    | Some p -> 
      let p' = (PlainAE.ae_message_unwrap #ae_i p) in 
      Some p'
    | None -> None)
