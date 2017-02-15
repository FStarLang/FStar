(**
   TODO: - Documentation, some cleanup.
	 - make decrypt a total function.
*)
module HyE.DH

open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.List.Tot

open CoreCrypto
open Platform.Bytes

open HyE.Indexing
open HyE.PlainDH
open HyE.Flags

module HH = FStar.HyperHeap
module MM = MonotoneMap

assume val dh_share_size : nat
assume val dh_exponent_size : nat
type dh_share = lbytes dh_share_size
abstract type dh_exponent = lbytes dh_exponent_size

assume val dh_gen_key: unit -> Tot (dh_share*dh_exponent)

type keysize = aeadKeySize AES_128_GCM
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)

type log_t (i:id) (r:rid) = m_rref r (seq (entry:(PlainDH.key*dh_share){ae_fixed (PlainDH.get_index (fst entry))})) grows

noeq type dh_pkey = 
  | DH_pkey:  #pk_i:id -> #region:rid ->rawpk:dh_share -> log:log_t pk_i region -> dh_pkey


noeq abstract type dh_skey =
  | DH_skey: #sk_i:id -> rawsk:dh_exponent -> pk:dh_pkey{pk.pk_i=sk_i} -> dh_skey 

val get_index: dh_skey -> Tot(id)
let get_index k = k.sk_i

val keygen: #i:id -> (parent:rid{disjoint id_honesty_table_region parent}) -> ST (dh_pair:(k:dh_pkey{k.pk_i=i}) * (k:dh_skey{k.sk_i=i}))
  (requires (fun h -> fresh i h /\ MM.fresh id_honesty_table i h))
  (ensures (fun h0 k h1 ->
    let (s:Set.set (HH.rid)) = Set.union (Set.singleton parent) (Set.singleton id_freshness_table_region) in
    modifies s h0 h1
    /\ MM.fresh id_honesty_table i h1
    /\ unfresh i
//  let (pk,sk) = k in
//  safe_key_gen parent pk h0 h1
  ))
let keygen #i parent =
  make_unfresh i;
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  let dh_share,dh_exponent = dh_gen_key() in
  let dh_pk = DH_pkey #i #region dh_share log in
  let dh_sk = DH_skey #i dh_exponent dh_pk in
  let h1 = ST.get() in
  dh_pk,dh_sk


(**
   This function takes a dh_share to the power of a dh_exponent.
   TODO: Actually link to functional code in CoreCrypto?
*)
assume val dh_exponentiate: dh_share -> dh_exponent -> Tot aes_key

type safe_log_append pk entry h0 h1 =
    modifies_one pk.region h0 h1 
    /\ m_contains pk.log h1
    /\ m_sel h1 pk.log == snoc (m_sel h0 pk.log) entry
    /\ witnessed (at_least (Seq.length (m_sel h0 pk.log)) entry pk.log)

(**
   If we prf_odh is true, the output of this function is random, if both 
   share and exponent are honest.
*)
val prf_odh_snd: sk:dh_skey -> pk:dh_pkey -> ST (PlainDH.key)
  ( requires (fun _ -> ae_fixed (generate_ae_id sk.sk_i pk.pk_i)))
  ( ensures (fun _ k _ -> 
    HyE.AE.get_index k = generate_ae_id pk.pk_i sk.sk_i
  ))
let prf_odh_snd dh_snd_sk dh_rcv_pk =
  let pk_id = dh_rcv_pk.pk_i in
  let sk_id = dh_snd_sk.sk_i in
  let i = generate_ae_id pk_id sk_id in
  let ae_honest_i = ae_honestST i in
  if ae_honest_i && prf_odh then
    let k' = PlainDH.keygen i dh_rcv_pk.region in
    write_at_end dh_rcv_pk.log (k',dh_snd_sk.pk.rawpk);
    k'
  else
    let real_k = dh_exponentiate dh_rcv_pk.rawpk dh_snd_sk.rawsk in
    let k=PlainDH.coerce_key i dh_rcv_pk.region real_k in
    k

val equal_share: dh_sh:dh_share -> entry:(PlainDH.key*dh_share) -> Tot bool
let equal_share dh_sh entry =
  snd entry = dh_sh


val prf_odh_rcv: #(sk_id:id{fixed sk_id}) -> dh_sh:dh_share -> dh_sk:dh_skey -> ST (k:PlainDH.key)//{fst (AE.get_index k) = sk_id})
  (requires (fun h0 -> True))
  (ensures (fun h0 k h1 ->
    ae_fixed (PlainDH.get_index k)
  ))
let prf_odh_rcv #sk_id dh_sh dh_rcv_sk =
  let honest_sk_id = honestST sk_id in
  if honest_sk_id && prf_odh then
    let log = m_read dh_rcv_sk.pk.log in
    let entry = seq_find (equal_share dh_sh) log in
    match entry with
    | Some (k',_) -> k'
    | None -> 
      let dis_id = generate_fresh_id() in
      make_unfresh dis_id;
      make_dishonest dis_id;
      let i = generate_ae_id sk_id dis_id in
      let raw_k = dh_exponentiate dh_sh dh_rcv_sk.rawsk in
      PlainDH.coerce_key i dh_rcv_sk.pk.region raw_k
  else
    let dis_id = generate_fresh_id() in
    make_unfresh dis_id;
    make_dishonest dis_id;
    let i = generate_ae_id sk_id dis_id in
    let raw_k = dh_exponentiate dh_sh dh_rcv_sk.rawsk in
    PlainDH.coerce_key i dh_rcv_sk.pk.region raw_k
