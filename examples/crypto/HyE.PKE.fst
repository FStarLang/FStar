(**
   TODO: - Documentation, some cleanup.
	 - make decrypt a total function.
*)
module HyE.PKE  (* intuitively, parameterized by both PlainPKE and RSA *)

open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.List.Tot

open CoreCrypto
open Platform.Bytes

open HyE.PlainPKE
open HyE.Flags
open HyE.RSA
open HyE.Indexing


type cipher = RSA.cipher

assume val ciphersize : nat

type log_t (i:pke_id) (r:rid) = m_rref r (seq (protected_pke_plain i*cipher)) grows

noeq abstract type pkey (pke_i:pke_id) = 
  | PKey: #region:rid -> rawpk:RSA.pkey -> log: log_t pke_i region -> pkey pke_i

val access_pk_raw: #i:pke_id -> pkey i -> Tot RSA.pkey
let access_pk_raw #i pk =
  pk.rawpk

noeq abstract type skey (i:pke_id) =
  | SKey: rawsk:RSA.skey -> (pk:pkey i)-> skey i

let safe_key_gen #i parent (pk:pkey i) m0 m1 =
    modifies Set.empty m0 m1
    /\ m_contains pk.log m1
    /\ extends pk.region parent
    /\ fresh_region pk.region m0.h m1.h
    /\ m_sel m1 pk.log == createEmpty

val keygen: #i:pke_id -> (parent:rid) -> ST (pkey i * skey i)
  (requires (fun h -> True))
  (ensures (fun h0 k h1 -> 
  let (pk,sk) = k in
  safe_key_gen parent pk h0 h1
  ))
let keygen #i parent =
  let (pkey_raw, skey_raw) = (random RSA.pk_size),(random RSA.sk_size) in
  let region = new_region parent in
  let log = alloc_mref_seq region createEmpty in
  let pkey = PKey #i #region pkey_raw log in
  let skey = SKey #i skey_raw pkey in
  pkey, skey
  

type safe_log_append pk entry h0 h1 =
    modifies_one pk.region h0 h1 
    /\ m_contains pk.log h1
    /\ m_sel h1 pk.log == snoc (m_sel h0 pk.log) entry
    /\ witnessed (at_least (Seq.length (m_sel h0 pk.log)) entry pk.log)

val encrypt: #i:pke_id -> (pk:pkey i) -> p:protected_pke_plain i -> ST RSA.cipher
  (requires (fun h0 -> True
    (*m_contains k.log h0*)))
  (ensures  (fun h0 c h1 -> True ))
   // safe_log_append pk (p,c) h0 h1))
let encrypt #i pk p =
  m_recall pk.log;
  let p' = if pke_ind_cca && pke_honest i then createBytes (AE.keysize) 0z else PlainPKE.repr p in
  let c = RSA.enc pk.rawpk p' in
  write_at_end pk.log (p,c);
  c

  
val decrypt: #i:pke_id -> (sk:skey i) -> (c:RSA.cipher) -> ST (option (protected_pke_plain i))
  (requires (fun h -> True (* Could require Map.contains h0 k.region *)))
  (ensures  (fun h0 p h1 -> True))
    //modifies_none h0 h1))
let decrypt #i sk c =
  let log = m_read (sk.pk.log) in
  let pke_p = seq_find (fun (_,c') -> c=c') log in
    match (pke_ind_cca),pke_p with
    | true,Some (m,c)  -> Some(m)
    | _,_ -> 
      (match RSA.dec sk.rawsk c with
	| Some p' ->
	    let disId = dishonest_ae_id i in
	    Some (PlainPKE.coerce #(disId) sk.pk.region p')
	| None -> None)
