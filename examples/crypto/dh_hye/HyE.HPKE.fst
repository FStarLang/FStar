module HyE.HPKE

open Platform.Bytes
open FStar.HyperHeap
open FStar.HyperStack
open HyE.Flags
open HyE.AE
open HyE.DH
open HyE.PlainHPKE
open HyE.PlainAE
open HyE.PlainDH
open HyE.Indexing

module B = Platform.Bytes
module MM = MonotoneMap
type rid = FStar.Monotonic.Seq.rid

assume val hpke_key_region: (r:rid{extends r root /\ is_eternal_region r /\ is_below r root /\ disjoint id_freshness_table_region r /\ disjoint id_honesty_table_region r})

noeq abstract type hpke_pkey (pk_id:id) =
  | PKey: #region:rid -> dh_pk:dh_pkey{dh_pk.pk_i=pk_id} -> hpke_pkey pk_id

noeq abstract type hpke_skey (sk_id:id) =
  | SKey: dh_sk:dh_skey -> hpke_pk:hpke_pkey sk_id -> hpke_skey sk_id

val keygen: #(i:id) -> ST (hpke_pkey i * hpke_skey i)
  (requires (fun h0 -> fresh i h0))
  (ensures (fun h0 keypair h1 -> True))
let keygen #i =
  let (dh_pk, dh_sk) = DH.keygen #i hpke_key_region in
  let region = new_region hpke_key_region in
  let hpke_pk = PKey #i #region dh_pk in
  hpke_pk, SKey #i dh_sk hpke_pk

type c = DH.dh_share * AE.cipher //lbytes(PKE.ciphersize + AE.ciphersize)


val encrypt: #(pk_i:id) -> #(eph_i:id)-> hpke_pkey pk_i -> p:protected_hpke_plain{PlainHPKE.get_index p = generate_ae_id pk_i eph_i} -> ST c
  (requires (fun h0 -> 
    fixed pk_i /\ fresh eph_i h0
  ))
  (ensures (fun h0 c h1 -> True))
let encrypt #pk_i #eph_i pk p =
  let eph_dh_pk,eph_dh_sk = DH.keygen #eph_i hpke_key_region in
  make_honest eph_i;
  let k = prf_odh_snd eph_dh_sk pk.dh_pk in
  let ae_i = generate_ae_id pk_i eph_i in
  let ae_honest_ae_i = ae_honestST ae_i in
  let ae_m = ae_message_wrap #ae_i p in
  eph_dh_pk.rawpk,(AE.encrypt #ae_i k ae_m)


val decrypt: #(sk_i:id{fixed sk_i}) -> hpke_skey sk_i -> c -> St (option (p:protected_hpke_plain))//{fst (PlainHPKE.get_index p) = sk_i })
let decrypt #sk_i sk c =
  let (dh_sh,ae_c) = c in 
  let k = prf_odh_rcv #sk_i dh_sh sk.dh_sk in
  let ae_i = AE.get_index k in
  match AE.decrypt #ae_i k ae_c with
  | Some p -> 
    let p' = (PlainAE.ae_message_unwrap #ae_i p) in 
    Some p'
  | None -> None
