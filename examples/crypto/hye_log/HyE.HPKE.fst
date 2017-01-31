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
noeq abstract type hpke_pkey (pk_id:pke_id) = 
  | PKey: #region:rid -> pke_pk:PKE.pkey pk_id -> hpke_pkey pk_id

noeq abstract type hpke_skey (sk_id:pke_id) =
  | SKey: pke_sk:PKE.skey sk_id -> hpke_pk:hpke_pkey sk_id -> hpke_skey sk_id
  

val keygen: #i:pke_id -> rid -> hpke_pkey i * hpke_skey i
let keygen #i (parent:rid) =
  let (pke_pk, pke_sk) = PKE.keygen parent in
  let region = new_region parent in
  let hpke_pk = PKey #i #region pke_pk in
  hpke_pk, SKey pke_sk hpke_pk

val coerce_key: #i:pke_id{not (pke_honest i)} -> rid -> PKE.pkey i-> Tot (hpke_pkey i)
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
val encrypt: #(pke_i:pke_id) -> hpke_pkey pke_i -> p:protected_hpke_plain -> ST c
  (requires (fun _ -> 
    let ae_i = PlainHPKE.get_index p in
    not (pke_honest pke_i) ==> not (honest ae_i)
  ))
  (ensures (fun _ _ _ -> True))
let encrypt #i pk p =
  let region = new_region pk.region in
  let ae_i = PlainHPKE.get_index p in
  let k = AE.keygen #ae_i region in 
  let pke_p = Prot_pke_p ae_i k in
  let p' =
    match hpke_ind_cca && honest ae_i with
    | true -> p
    | false -> PlainHPKE.repr p
  in
  let ae_m = ae_message_wrap p' in
  ((PKE.encrypt pk.pke_pk pke_p) ,(AE.encrypt k ae_m))

    
val decrypt: #i:pke_id -> hpke_skey i -> c -> option (protected_hpke_plain)
let decrypt #i sk c =
  let (c0,c1) = c in 
  let pke_plain = PKE.decrypt sk.pke_sk c0 in
  match pke_plain with 
  | Some p -> 
    (match AE.decrypt p.k c1 with
    | Some ae_prot_p -> 
      let ae_m = PlainAE.ae_message_unwrap ae_prot_p in
      let ae_i = PlainAE.extract_id ae_m in
      if honest ae_i && hpke_ind_cca then
	Some ae_m
      else
	Some (PlainHPKE.coerce #ae_i ae_m)
    | None -> None)
  | None   -> None
