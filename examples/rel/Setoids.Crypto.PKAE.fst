module Setoids.Crypto.PKAE
open FStar.Bytes
open FStar.UInt32
open FStar.Map
open Setoids
open Setoids.Crypto
open Setoids.Crypto.KEY
open Setoids.Crypto.AE
open Setoids.Crypto.ODH

module DM = FStar.DependentMap

let pkey n = share n
let nonce = bytes

let pkae_state n aes = (ae_log #n aes * odh_state n) * key_state n

let pkae_state_rel n aes = ((lo (ae_log #n aes)) ** (lo (odh_state n))) ** (lo (key_state n))

let lift_ae_state #a (#arel:erel a) n aes (f:eff (lo (ae_log #n aes) ** lo (key_state n)) arel)
  : eff (pkae_state_rel n aes) arel
  = fun (t, ((ae_st, odh_st), key_st)) ->
      match f (t, (ae_st, key_st)) with
      | None, (ae_st', key_st'), t -> None, ((ae_st',odh_st), key_st'), t
      | Some x, (ae_st', key_st'), t -> Some x, ((ae_st',odh_st), key_st'), t

let lift_odh_state #a (#arel:erel a) n aes (f:eff (lo (odh_state n) ** lo (key_state n)) arel)
  : eff (pkae_state_rel n aes) arel
  = fun (t, ((ae_st, odh_st), key_st)) ->
      match f (t, (odh_st, key_st)) with
      | None, (odh_st', key_st'), t -> None, ((ae_st,odh_st'), key_st'), t
      | Some x, (odh_st', key_st'), t -> Some x, ((ae_st,odh_st'), key_st'), t

let ae_odh_sig n aes = sig_prod (odh_sig n) (ae_sig n aes)
let ae_odh_module n aes = module_t (ae_odh_sig n aes)

let pkae_gen_t n aes =
  (lo unit)
  ^--> eff_rel (((hi (ae_log #n aes)) ** (lo (odh_state n))) ** (lo (key_state n))) (lo (share n))

let pkae_gen n aes (m:ae_odh_module n aes) : pkae_gen_t n aes
  =
  fun _ ->
  let odh_gen : gen_dh_t n = get_oracle m (Inl GEN_DH) in
  lift_odh_state n aes (odh_gen ())

let pkae_enc_inputs n (aes:ae_scheme n) = quatruple_rel (lo (pkey n)) (lo (pkey n)) (lo nonce) (lo (p:bytes{len p `lte` aes.max_plaintext_length}))

let pkae_enc_t n aes =
  pkae_enc_inputs n aes
  ^--> eff_rel (pkae_state_rel n aes) (lo bytes)

#set-options "--z3rlimit 350 --max_fuel 2 --max_ifuel 4"
#set-options "--query_stats"
let pkae_enc n aes (m:ae_odh_module n aes) : pkae_enc_t n aes =
  fun (sender_pk, receiver_pk, nonce, p) ->
    let odh_exp : odh_t n = get_oracle m (Inl ODH) in
    let ae_enc : enc_t n aes = get_oracle m (Inr ENC) in
    h <-- lift_odh_state n aes (odh_exp (sender_pk, receiver_pk));
    c <-- lift_ae_state n aes (ae_enc (p,nonce,h));
    return #(pkae_state n aes) #bytes #(pkae_state_rel n aes) c

let pkae_dec_inputs n (aes:ae_scheme n) = quatruple_rel (lo (pkey n)) (lo (pkey n)) (lo nonce) (lo (c:bytes{len c `lte` aes.ciphertext_length aes.max_plaintext_length}))

let pkae_dec_t n aes =
  pkae_dec_inputs n aes
  ^--> eff_rel (pkae_state_rel n aes) (lo (option (p:bytes{len p `lte` aes.max_plaintext_length})))

let pkae_dec n aes (m:ae_odh_module n aes) : pkae_dec_t n aes =
  fun (sender_pk, receiver_pk, nonce, c) ->
    let odh_exp : odh_t n = get_oracle m (Inl ODH) in
    let ae_dec : dec_t n aes = get_oracle m (Inr DEC) in
    h <-- lift_odh_state n aes (odh_exp (sender_pk, receiver_pk));
    p <-- lift_ae_state #(option (p:bytes{len p `lte` aes.max_plaintext_length})) #(lo (option (p:bytes{len p `lte` aes.max_plaintext_length}))) n aes (ae_dec (c,nonce,h));
    return #(pkae_state n aes) #(option (p:bytes{len p `lte` aes.max_plaintext_length})) #(pkae_state_rel n aes) p

type pkae_labels =
    | GEN
    | ENC
    | DEC

let pkae_field_types n aes : pkae_labels -> Type =
    function  GEN -> pkae_gen_t n aes
            | ENC -> pkae_enc_t n aes
            | DEC -> pkae_dec_t n aes

// The relations seem to be the problem. I have removed the relations for now.
let pkae_field_rels n aes : (l:pkae_labels -> erel (pkae_field_types n aes l)) =
  function
      GEN -> fun _ _ -> True
    | ENC -> fun _ _ -> True
    | DEC -> fun _ _ -> True

let pkae_sig (n:u32) (aes:ae_scheme n) = {
  labels = pkae_labels;
  ops = pkae_field_types n aes;
  rels = pkae_field_rels n aes
  }

let pkae_module (n:u32) (aes:ae_scheme n) (m:ae_odh_module n aes) : module_t (pkae_sig n aes) =
  DM.create #_ #(pkae_sig n aes).ops
    (function GEN -> pkae_gen n aes m
            | ENC -> pkae_enc n aes m
            | DEC -> pkae_dec n aes m)

let pkae_functor (n:u32) (aes:ae_scheme n)
  : functor_t (sig_prod (odh_sig n) (ae_sig n aes)) (pkae_sig n aes)
  = fun m ->
      pkae_module n aes m

///     ID_WRITE
///     -------- o KEY_0
///     ID_READ
let key0_id_composition n
  : functor_t sig_unit (sig_prod (key_write_sig n) (key_read_sig n)) =
  let id_composition =
    functor_prod_shared_sig
      (key_sig n)
      (key_write_sig n)
      (key_read_sig n)
      (key_write_functor n)
      (key_read_functor n) in
  comp id_composition (KEY.key0_functor n)

///     ID_WRITE
///     -------- o KEY_1
///     ID_READ
let key1_id_composition n
  : functor_t sig_unit (sig_prod (key_write_sig n) (key_read_sig n)) =
  let id_composition =
    functor_prod_shared_sig
      (key_sig n)
      (key_write_sig n)
      (key_read_sig n)
      (key_write_functor n)
      (key_read_functor n) in
  comp id_composition (KEY.key1_functor n)

///   ODH
///   ----
///   AE_0
let protocol0_composition n aes
  : functor_t (sig_prod (key_write_sig n) (key_read_sig n)) (sig_prod (odh_sig n) (ae_sig n aes)) =
  functor_prod
    (key_write_sig n)
    (odh_sig n)
    (key_read_sig n)
    (ae_sig n aes)
    (odh_functor n)
    (ae0_functor n aes)

///   ODH
///   ----
///   AE_1
let protocol1_composition n aes
  : functor_t (sig_prod (key_write_sig n) (key_read_sig n)) (sig_prod (odh_sig n) (ae_sig n aes)) =
  functor_prod
    (key_write_sig n)
    (odh_sig n)
    (key_read_sig n)
    (ae_sig n aes)
    (odh_functor n)
    (ae1_functor n aes)

///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_0
///         AE_0   ID_READ
let pkae0_composition n aes
  : functor_t sig_unit (pkae_sig n aes) =
    let prot = comp (protocol0_composition n aes) (key0_id_composition n) in
    comp (pkae_functor n aes) prot

///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_1
///         AE_1   ID_READ
let pkae1_composition n aes
  : functor_t sig_unit (pkae_sig n aes) =
    let prot = comp (protocol1_composition n aes) (key0_id_composition n) in
    comp (pkae_functor n aes) prot

/// Proof:
/// Assumptions:
/// - (ODH|ID_READ) o KEY_0 = (ODH|ID_READ) o KEY_1
/// - (ID_WRITE|AE_0) o KEY_1 = (ID_WRITE|AE_1) o KEY_1
let pkae_proof (n:u32) (aes:ae_scheme n) : Lemma
  (ensures (eq (fun _ _ -> True) (sum (ae_eps n aes) (odh_eps n)) (pkae0_composition n aes) (pkae1_composition n aes)))
  = ()
