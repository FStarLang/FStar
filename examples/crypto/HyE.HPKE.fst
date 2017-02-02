(**
This is the top level module for the hybid encryption example. The structure of the example is as follows.

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
open HyE.PKE
open HyE.PlainHPKE
open HyE.PlainAE
open HyE.PlainPKE
open HyE.Indexing

module B = Platform.Bytes


type rid = FStar.Monotonic.Seq.rid

(**
   The HPKE key types contain a region in which they live, as well as the concrete PKE key
   that is used for the encryption/decryption. The secret key is abstract.
*)
noeq abstract type hpke_pkey = 
  | PKey: #pk_id:pke_id -> #region:rid -> pke_pk:PKE.pkey pk_id -> hpke_pkey

noeq abstract type hpke_skey =
  | SKey: #sk_id:pke_id -> pke_sk:PKE.skey sk_id -> hpke_pk:hpke_pkey -> hpke_skey
  
(**
   TODO: Have a table with public keys, binding pks to ids.
     - look at miTLS:Sig
*)
val keygen: rid -> St (hpke_pkey * hpke_skey)
let keygen (parent:rid) =
  let pk_id = fresh_pke_id() in
  let (pke_pk, pke_sk) = PKE.keygen #pk_id parent in
  let region = new_region parent in
  let hpke_pk = PKey #pk_id #region pke_pk in
  hpke_pk, SKey #pk_id pke_sk hpke_pk

val coerce_key: #i:pke_id{not (pke_honest i)} -> rid -> PKE.pkey i -> Tot (hpke_pkey)
let coerce_key #i parent pke_pk =
  PKey #i #parent pke_pk

(**
   The ciphertext of HPKE consists of a PKE ciphertext (containing the ephemeral AE key)
   and an AE ciphertext containing said key.
*)
type c = PKE.cipher * AE.cipher //lbytes(PKE.ciphersize + AE.ciphersize)

(**
   For every new message we encrypt, we generate a new pke_id. If that
   pke_id is honest (which is only possible if pke is idealized), then
   we encrypt the protected_hpke_plain. Else we strip it of its 
   protection and encrypt the plain representation.
*)
val encrypt: #(pk_id:pke_id) -> pk:hpke_pkey{pk.pk_id=pk_id} -> p:protected_hpke_plain pk_id -> St c
let encrypt #pk_id pk p =
  let region = new_region pk.region in
  let k_id = fresh_ae_id pk_id in
  let k = AE.keygen #k_id region in 
  let ae_m = p in
  ((PKE.encrypt #pk_id pk.pke_pk k) ,(AE.encrypt #k_id k ae_m))

    
val decrypt: #pk_id:pke_id -> sk:hpke_skey{sk.sk_id=pk_id} -> c -> St (option (protected_hpke_plain pk_id))
let decrypt #pk_id sk c =
  let (c0,c1) = c in 
  let k_option = PKE.decrypt sk.pke_sk c0 in
  match k_option with 
  | Some k -> 
    let k_id = get_index k in
    (match AE.decrypt #k_id k c1 with
    | Some ae_m -> Some (PlainAE.ae_unwrap ae_m)
    | None -> None)
  | None   -> None
