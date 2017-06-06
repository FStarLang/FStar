module HyE.HCCA2
open FStar.HyperStack.All
open FStar.HyperStack.ST
open HyE.Plain
open HyE.PlainPKE
open Platform.Bytes
open FStar.HyperHeap
open FStar.HyperStack

module B = Platform.Bytes
module P = HyE.Plain
module C = HyE.CCA2
module A = HyE.AE


(* we idealize first CCA2, then AE *)

type rid = FStar.Monotonic.Seq.rid

noeq abstract type pkey = 
  | PKey: #region:rid -> rawpk:RSA.pkey -> cca_pk:CCA2.pkey  -> pkey

let access_pkraw (pk:pkey) =
  PKey?.rawpk pk

noeq abstract type skey =
  | SKey: cca_sk:CCA2.skey -> pk:pkey  -> skey    type p = P.t

type c = C.cipher * A.cipher //lbytes(CCA2.ciphersize + AE.ciphersize)

val keygen: rid -> ML (pkey * skey)
val encrypt: pkey -> p -> ML c 
val decrypt: skey -> c -> ML (option p )


let keygen (parent:rid) =
  let cca_pk, cca_sk = C.keygen parent in
  let region = new_region parent in
  let pkey = PKey #region (CCA2.access_pk_raw cca_pk) cca_pk in
  pkey, SKey cca_sk pkey


let encrypt pk t =
  let region = new_region pk.region in
  let k = A.keygen region in 
  ((C.encrypt pk.cca_pk k) ,(A.encrypt k t))


let decrypt sk c =
  let (c0,c1) = c in 
  match C.decrypt sk.cca_sk c0 with 
  | Some k -> AE.decrypt k c1
  | None   -> None
