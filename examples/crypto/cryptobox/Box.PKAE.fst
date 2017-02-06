(**
This is the top level module for the hybrid encryption example. The structure of the example is as follows.

  * Box.AE contains the relevant functions for authenticated encryption, including leaking of plaintext and coersion of keys.
    Its encryption/decryption function contain calls to the concrete functions in CoreCrypto.
  * Box.PKE contains the relevant functions for CCA-secure public-key encryption. Its encryption/decryption functions contain calls to Box.RSA.
  * Box.Flags contains the flags controlling the idealization of modules depending on the assumptions on underlying cryptographic primitives.
  * Box.PlainAE contains functions to convert abstract types to concrete types and the other way around for symmetric encryption content.
  * Box.PlainPKE fulfills the same role as Box.Plain but for public-key encryption.
  * Box.RSA contains references to external functions implementing the actual functionality. However, these do currently not exist.

The cryptographic keys are stored in memory in the following manner. Beneath the memory root, the public key as used in CCA2 is stored.
As children of the public key, each private key (honest and dishonest) live in their own memory regions.

TODO: 
   * Actually structure the memory layout that way.
   * Investigate where the secret key is actually stored.
   * Figure out, why the precondition in Box.AE.encrypt is not met. (recall <-> m_contains...)
   * Sketch overall proof structure
*)
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

type rid = FStar.Monotonic.Seq.rid

(**
   The PKAE key types contain a region in which they live, as well as the concrete PKE key
   that is used for the encryption/decryption. The secret key is abstract.
*)
noeq abstract type pkae_pkey (pk_id:id) =
  | PKey: dh_pk:dh_pkey{DH.pk_get_index dh_pk=pk_id} -> pkae_pkey pk_id

noeq abstract type pkae_skey (sk_id:id) =
  | SKey: dh_sk:dh_skey{DH.sk_get_index dh_sk=sk_id} -> pkae_pk:pkae_pkey sk_id -> pkae_skey sk_id

val keygen: #(i:id) -> St (pkae_pkey i * pkae_skey i)
let keygen #i =
  let (dh_pk, dh_sk) = DH.keygen #i in
  let pkae_pk = PKey #i dh_pk in
  pkae_pk, SKey #i dh_sk pkae_pk

(**
   The ciphertext of PKAE consists of a PKE ciphertext (containing the ephemeral AE key)
   and an AE ciphertext containing said key.
*)
type c = DH.dh_share * AE.cipher //lbytes(PKE.ciphersize + AE.ciphersize)


val encrypt: #(pk_id:id) -> #(sk_id:id) -> pkae_pkey pk_id -> pkae_skey sk_id -> p:protected_pkae_plain{PlainPKAE.get_index p = (pk_id,sk_id) || PlainPKAE.get_index p = (sk_id,pk_id)} -> St c 
let encrypt #pk_id #sk_id pkae_pk  pkae_sk p =
  let k = prf_odh pkae_sk.dh_sk pkae_pk.dh_pk in
  let ae_i = AE.get_index k in
  assert(AE.get_index k = ae_i || AE.get_index k = (snd ae_i, fst ae_i));
//  assert (DH.get_index eph_dh_sk = snd ae_i);
//  assert (pk.dh_pk.pk_i = fst ae_i);
//  assert (DH.get_index eph_dh_sk = eph_i);
//  assert (pk.dh_pk.pk_i = pk_i);
//  assert (ae_i = (pk_i,eph_i));
  let ae_m = ae_message_wrap #ae_i p in
  //let dh_m = dh_message_wrap #pk.i eph_dh_pk.rawpk in
  DH.pk_get_rawpk pkae_pk.dh_pk,(AE.encrypt #ae_i k ae_m)


val decrypt: #(sk_id:id) -> pkae_skey sk_id -> #(pk_id:id) -> pkae_pkey sk_id -> c -> St(option (p:protected_pkae_plain//{PlainPKAE.get_index p = (sk_i,pk_i) }
))
let decrypt #sk_id sk #pk_id pk c =
  let (dh_sh,ae_c) = c in 
  let k = prf_odh sk.dh_sk pk.dh_pk  in
  let ae_i = AE.get_index k in
  (match AE.decrypt #ae_i k ae_c with
  | Some p -> 
    let p' = (PlainAE.ae_message_unwrap #ae_i p) in 
    Some p'
  | None -> None)
