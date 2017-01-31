(**
This is the top level module for the hybrid encryption example. The structure of the example is as follows.

  * HyE.AE contains the relevant functions for authenticated encryption, including leaking of plaintext and coersion of keys.
    Its encryption/decryption function contain calls to the concrete functions in CoreCrypto.
  * HyE.PKE contains the relevant functions for CCA-secure public-key encryption. Its encryption/decryption functions contain calls to HyE.RSA.
  * HyE.Flags contains the flags controlling the idealization of modules depending on the assumptions on underlying cryptographic primitives.
  * HyE.PlainAE contains functions to convert abstract types to concrete types and the other way around for symmetric encryption content.
  * HyE.PlainPKE fulfills the same role as HyE.Plain but for public-key encryption.
  * HyE.RSA contains references to external functions implementing the actual functionality. However, these do currently not exist.

The cryptographic keys are stored in memory in the following manner. Beneath the memory root, the public key as used in CCA2 is stored.
As children of the public key, each private key (honest and dishonest) live in their own memory regions.

TODO: 
   * Actually structure the memory layout that way.
   * Investigate where the secret key is actually stored.
   * Figure out, why the precondition in HyE.AE.encrypt is not met. (recall <-> m_contains...)
   * Sketch overall proof structure
*)
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

type rid = FStar.Monotonic.Seq.rid

(**
   The HPKE key types contain a region in which they live, as well as the concrete PKE key
   that is used for the encryption/decryption. The secret key is abstract.
*)
noeq abstract type hpke_pkey (pk_id:id) =
  | PKey: #region:rid -> dh_pk:dh_pkey{dh_pk.pk_i=pk_id} -> hpke_pkey pk_id

noeq abstract type hpke_skey (sk_id:id) =
  | SKey: dh_sk:dh_skey -> hpke_pk:hpke_pkey sk_id -> hpke_skey sk_id

val keygen: #(i:id) -> rid -> hpke_pkey i * hpke_skey i
let keygen #i (parent:rid) =
  let (dh_pk, dh_sk) = DH.keygen #i parent in
  let region = new_region parent in
  let hpke_pk = PKey #i #region dh_pk in
  hpke_pk, SKey #i dh_sk hpke_pk

(**
   The ciphertext of HPKE consists of a PKE ciphertext (containing the ephemeral AE key)
   and an AE ciphertext containing said key.
*)
type c = DH.dh_share * AE.cipher //lbytes(PKE.ciphersize + AE.ciphersize)


(**
   For every new message we encrypt, we generate a new id. If that
   id is honest (which is only possible if pke is idealized), then
   we encrypt the protected_hpke_plain. Else we strip it of its 
   protection and encrypt the plain representation.
*)
val encrypt: #(i:id) -> hpke_pkey i -> protected_hpke_plain i -> St c 
let encrypt #i pk p =
  let region = new_region pk.region in
  let eph_i = createId () in
  let eph_dh_pk,eph_dh_sk = DH.keygen #eph_i region in
  let k = prf_odh_snd eph_dh_sk pk.dh_pk in
  let ae_i = AE.getIndex k in
  assert (getIndex eph_dh_sk = snd ae_i);
  assert (pk.dh_pk.pk_i = fst ae_i);
  assert (getIndex eph_dh_sk = eph_i);
  assert (pk.dh_pk.pk_i = i);
  assert (ae_i = (i,eph_i));
  let p' = 
    match hpke_ind_cca && ae_honest ae_i with
    | true -> p
    | false -> PlainHPKE.repr p
  in
  let ae_m = ae_message_wrap #ae_i p' in
  //let dh_m = dh_message_wrap #pk.i eph_dh_pk.rawpk in
  eph_dh_pk.rawpk,(AE.encrypt #ae_i k ae_m)


val decrypt: #(i:id) -> hpke_skey i -> c -> option (protected_hpke_plain i)
let decrypt #i sk c =
  let (dh_sh,ae_c) = c in 
  let ae_i,k = prf_odh_rcv #i dh_sh sk.dh_sk in
  let hpke_p =
    (match AE.decrypt #ae_i k ae_c with
    | Some p -> Some (PlainAE.ae_message_unwrap #ae_i p)
    | None -> None)
  in
  match hpke_p with
  | Some p' -> 
    (if ae_honest ae_i && hpke_ind_cca then
      Some p'
    else 
      Some (PlainHPKE.coerce p'))
  | None -> None
