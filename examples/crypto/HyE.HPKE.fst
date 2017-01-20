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
   * Remove redundancy from the way the public key is stored.
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
open HyE.PKE
open HyE.PlainHPKE
open HyE.PlainAE
open HyE.Indexing

module B = Platform.Bytes


type rid = FStar.Monotonic.Seq.rid

(**
   The HPKE key types contain a region in which they live, as well as the concrete PKE key
   that is used for the encryption/decryption. The secret key is abstract.
*)
noeq type hpke_pkey = 
  | PKey: #region:rid -> pke_pk:PKE.pkey  -> hpke_pkey

noeq abstract type hpke_skey =
  | SKey: pke_sk:PKE.skey -> hpke_pk:hpke_pkey -> hpke_skey
 
val keygen: rid -> hpke_pkey * hpke_skey
let keygen (parent:rid) =
  let (pke_pk, pke_sk) = PKE.keygen parent in
  let region = new_region parent in
  let hpke_pk = PKey #region pke_pk in
  hpke_pk, SKey pke_sk hpke_pk

(**
   The ciphertext of HPKE consists of a PKE ciphertext (containing the ephemeral AE key)
   and an AE ciphertext containing said key.
*)
type c = PKE.cipher * AE.cipher //lbytes(PKE.ciphersize + AE.ciphersize)

(**
   For every new message we encrypt, we generate a new id. If that
   id is honest (which is only possible if pke is idealized), then
   we encrypt the protected_hpke_plain. Else we strip it of its 
   protection and encrypt the plain representation.
*)
val encrypt: hpke_pkey -> protected_hpke_plain -> c 
let encrypt pk p =
  let region = new_region pk.region in
  let i = createId() in
  let k = AE.keygen i region in 
  // Deduplicate code here.
  if honest i then
    let msg = ae_message_wrap #i p in
    assume (AE.getIndex k == PlainAE.getIndex msg);
    ((PKE.encrypt pk.pke_pk k) ,(AE.encrypt k msg))
  else 
    let unprotected_p = PlainHPKE.repr p in
    let msg = ae_message_wrap #i unprotected_p in
    assume (AE.getIndex k == PlainAE.getIndex msg);
    ((PKE.encrypt pk.pke_pk k) ,(AE.encrypt k msg))
    
val decrypt: hpke_skey -> c -> option protected_hpke_plain
let decrypt sk c =
  let (c0,c1) = c in 
  match PKE.decrypt sk.pke_sk c0 with 
  | Some k -> 
    (match AE.decrypt k c1 with
    | Some ae_protected_p -> Some (PlainAE.ae_message_unwrap ae_protected_p)
    | None -> None)
  | None   -> None
