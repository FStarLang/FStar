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


assume val dh_share_size : nat
assume val dh_exponent_size : nat
type dh_share = lbytes dh_share_size
abstract type dh_exponent = lbytes dh_exponent_size

assume val dh_gen_key: unit -> St (dh_share*dh_exponent)

type keysize = aeadKeySize AES_128_GCM
type aes_key = lbytes keysize (* = b:bytes{B.length b = keysize} *)


noeq type entry (i:id) = 
  | DH_entry: ent_i:id -> ent_share:dh_share -> ent_key:PlainDH.key{AE.get_index ent_key = (i,ent_i)} -> entry i


type log_t (i:id) (r:rid) = m_rref r (seq (entry i)) grows


noeq type dh_pkey = 
  | DH_pkey:  #pk_i:id -> #region:rid ->rawpk:dh_share -> log:log_t pk_i region -> dh_pkey


noeq abstract type dh_skey =
  | DH_skey: #sk_i:id -> rawsk:dh_exponent -> pk:dh_pkey{pk.pk_i=sk_i} -> dh_skey 

val get_index: dh_skey -> Tot(id)
let get_index k = k.sk_i

val keygen: #i:id -> (parent:rid) -> ST (dh_pair:(k:dh_pkey{k.pk_i=i}) * (k:dh_skey{k.sk_i=i}))
  (requires (fun h -> True))
  (ensures (fun h0 k h1 -> True
//  let (pk,sk) = k in
//  safe_key_gen parent pk h0 h1
  ))
let keygen #i parent =
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  let dh_share,dh_exponent = dh_gen_key() in
  let dh_pk = DH_pkey #i #region dh_share log in
  let dh_sk = DH_skey #i dh_exponent dh_pk in
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
  ( requires (fun _ -> True))
  ( ensures (fun _ k _ -> Box.AE.get_index k = (pk.pk_i, sk.sk_i)
  ))
let prf_odh_snd dh_snd_sk dh_rcv_pk =
  let pk_id = dh_rcv_pk.pk_i in
  let sk_id = dh_snd_sk.sk_i in
  let i = pk_id, sk_id in
  let ae_honest_i = ae_honestST i in
  if ae_honest_i && prf_odh then
    let k' = PlainDH.keygen i dh_rcv_pk.region in
    write_at_end dh_rcv_pk.log (DH_entry sk_id dh_snd_sk.pk.rawpk k');
    k'
  else
    let real_k = dh_exponentiate dh_rcv_pk.rawpk dh_snd_sk.rawsk in
    let k=PlainDH.coerce_key i dh_rcv_pk.region real_k in
    k

val equal_share: sk_i:id -> pk_i:id -> dh_sh:dh_share -> e:entry sk_i -> Tot bool
let equal_share sk_i pk_i dh_sh e =
  match e with 
  | DH_entry ent_i ent_share _ -> ent_i=pk_i && ent_share = dh_sh


val prf_odh_rcv: #(sk_id:id) -> dh_sk:dh_skey{dh_sk.sk_i=sk_id} -> #(pk_id:id) -> dh_snd_pk:dh_pkey{dh_snd_pk.pk_i=pk_id} ->  St (k:PlainDH.key{AE.get_index k = (sk_id,pk_id)}
)
let prf_odh_rcv #sk_id dh_rcv_sk #pk_id dh_snd_pk  =
  let honest_i = ae_honestST (sk_id, pk_id) in
  if honest_i && prf_odh then
    let log = m_read dh_rcv_sk.pk.log in
    let e = seq_find (equal_share sk_id pk_id dh_snd_pk.rawpk) log in
    match e with
    | Some (DH_entry _ _ k') -> k'
    | None -> 
      let i = sk_id,pk_id in
//      let i = sk_id,dishonestId() in
      let raw_k = dh_exponentiate dh_snd_pk.rawpk dh_rcv_sk.rawsk in
      admit ();
      PlainDH.coerce_key i dh_rcv_sk.pk.region raw_k
  else
    let i =  sk_id,pk_id in
    let raw_k = dh_exponentiate dh_snd_pk.rawpk dh_rcv_sk.rawsk in
    PlainDH.coerce_key i dh_rcv_sk.pk.region raw_k
