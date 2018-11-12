module HyE.CCA2  (* intuitively, parameterized by both PlainPKE and RSA *)
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.HyperStack
open FStar.Seq
open FStar.Monotonic.Seq

open FStar.List.Tot
open HyE.PlainPKE
module RSA = HyE.RSA
module PlainPKE = HyE.PlainPKE

type rid = erid
type cipher = RSA.cipher
noeq type entry =
  | Entry : c:RSA.cipher
         -> p:PlainPKE.t
         -> entry

assume val ciphersize : nat

type log_t (r:rid) = m_rref r (seq entry) grows

noeq abstract type pkey = 
  | PKey: #region:rid -> rawpk:RSA.pkey -> log: log_t region -> pkey

abstract let access_pk_raw (pk:pkey) =
  PKey?.rawpk pk


noeq abstract type skey =
  | SKey: raw:RSA.skey -> pk:pkey -> skey

val keygen: parent:rid{HyperStack.ST.witnessed (region_contains_pred parent)} -> ML (pkey * skey)
let keygen parent  =
  let pkey_raw, skey_raw = RSA.gen () in
  let region = new_region parent in
  let log = alloc_mref_seq region Seq.empty in
  let pkey = PKey #region pkey_raw log in
  pkey, SKey skey_raw pkey


let encrypt pk (p:PlainPKE.t) : ML RSA.cipher =
  let p' = if HyE.Ideal.ind_cca then RSA.dummy else PlainPKE.repr p in
  let c = RSA.enc pk.rawpk p' in
  write_at_end pk.log (Entry c p);
  c


let decrypt sk (c:RSA.cipher) : ML (option (PlainPKE.t)) =
  let log = !(PKey?.log sk.pk) in
  match HyE.Ideal.ind_cca, seq_find (function Entry c' _ -> c=c') log with
  | true,  Some t  -> Some(Entry?.p t)
  | _,  _       -> None
  | false, _ ->
    (match RSA.dec sk.raw c with
     | Some(t') -> PlainPKE.coerce t'
     | None     -> None)
