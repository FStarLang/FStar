module Setoids.Crypto.PKAE
open FStar.Bytes
open FStar.UInt32
open FStar.Map
open Setoids
open Setoids.Crypto

module DM = FStar.DependentMap

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 0"
let pkey n = lbytes32 n
let skey n = lbytes32 n
let nonce = bytes

noeq type pkae_scheme (n:u32) =
  | PKAES:
  max_plaintext_length: u32 ->
  ciphertext_length: (plaintext_length:u32{plaintext_length `lte` max_plaintext_length} -> u32) ->
  gen: (eff (lo unit) (lo (pkey n) ** lo (skey n))) ->
  enc: (p:bytes -> pk:pkey n -> sk:skey n -> nonce:bytes -> eff (lo unit) (lo bytes)) ->
  dec: (c:bytes -> pk:pkey n -> sk:skey n -> nonce:bytes -> option (p:bytes{len p `lte` max_plaintext_length})) ->
  pkae_scheme n

let handle = bytes * bytes

let pkae_log_key = handle*bytes
let pkae_log_value n (pkaes:pkae_scheme n) = fun (h,nonce) -> option (bytes*p:bytes{len p `lte` pkaes.max_plaintext_length})

/// Map from nonces to a maps from ciphertext to plaintexts
/// Should the state be dependent on the AE scheme?
abstract let pkae_log n (pkaes:pkae_scheme n) =
  DM.t (handle*bytes) (pkae_log_value n pkaes)

let pkae_log_rel (n:u32) (pkaes:pkae_scheme n) = lo (pkae_log n pkaes)

abstract let skey_log n =
  DM.t (pkey n) (fun pk -> option (skey n))

let skey_log_rel n = lo (skey_log n)

let pkae_state n pkaes = pkae_log n pkaes * skey_log n

let pkae_state_rel n pkaes = pkae_log_rel n pkaes ** skey_log_rel n

let pkae_gen_t n pkaes =
  (lo unit)
    ^--> eff_rel (hi (pkae_log n pkaes) ** lo (skey_log n)) (lo (pkey n))

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 0"
let pkae_gen n pkaes : pkae_gen_t n pkaes
  =
  fun _ ->
    keypair <-- lift_tape pkaes.gen;
    let pk,sk = keypair in
    s <-- get;
    let sk_log:skey_log n = snd s in
    let pkae_log = fst s in
    let sk_log':skey_log n = DM.upd sk_log pk (Some sk) in
    put (pkae_log,sk_log') ;;
    return pk

let pkae_enc_inputs n (pkaes:pkae_scheme n) =
  quatruple_rel
    (lo (pkey n))
    (lo (pkey n))
    (lo nonce)
    (lo (p:bytes{len p `lte` pkaes.max_plaintext_length}))

let pkae_enc_t n pkaes =
  pkae_enc_inputs n pkaes
    ^--> eff_rel (pkae_state_rel n pkaes) (lo bytes)

let pkae0_enc n pkaes : pkae_enc_t n pkaes =
  fun (sender_pk, receiver_pk, nonce, p) ->
    s <-- get;
    let sk_log:skey_log n = snd s in
    let pkae_log = fst s in
    match DM.sel sk_log sender_pk with
    | None ->
      raise
    | Some sk ->
      let h =
        if int_of_bytes sender_pk <= int_of_bytes receiver_pk then
          (sender_pk,receiver_pk)
        else
          (receiver_pk,sender_pk)
      in
      match DM.sel #(pkae_log_key) #(pkae_log_value n pkaes) pkae_log (h,nonce) with
      | Some _ ->
        raise
      | None ->
        c <-- lift_tape (pkaes.enc p receiver_pk sk nonce);
        let pkae_log' = DM.upd #(pkae_log_key) #(pkae_log_value n pkaes) pkae_log (h,nonce) (Some (c,p)) in
        put (pkae_log',sk_log);;
        return c

let pkae1_enc n pkaes : pkae_enc_t n pkaes =
  fun (sender_pk, receiver_pk, nonce, p) ->
    s <-- get;
    let sk_log:skey_log n = snd s in
    let pkae_log = fst s in
    match DM.sel sk_log sender_pk with
    | None ->
      raise
    | Some sk ->
      let h =
        if int_of_bytes sender_pk <= int_of_bytes receiver_pk then
          (sender_pk,receiver_pk)
        else
          (receiver_pk,sender_pk)
      in
      match DM.sel #(pkae_log_key) #(pkae_log_value n pkaes) pkae_log (h,nonce) with
      | Some _ ->
        raise
      | None ->
        c <-- sample_multiple (pkaes.ciphertext_length (len p));
        let pkae_log' = DM.upd #(pkae_log_key) #(pkae_log_value n pkaes) pkae_log (h,nonce) (Some (c,p)) in
        put (pkae_log',sk_log);;
        return #_ #bytes c

let pkae_dec_inputs n (pkaes:pkae_scheme n) =
  quatruple_rel
    (lo (pkey n))
    (lo (pkey n))
    (lo nonce)
    (lo (c:bytes{len c `lte` pkaes.ciphertext_length pkaes.max_plaintext_length}))

let pkae_dec_t n pkaes =
  pkae_dec_inputs n pkaes
    ^--> eff_rel (pkae_state_rel n pkaes) (option_rel (lo (p:bytes{len p `lte` pkaes.max_plaintext_length})))

let pkae0_dec n pkaes : pkae_dec_t n pkaes =
  fun (sender_pk, receiver_pk, nonce, c) ->
    s <-- get;
    let sk_log:skey_log n = snd s in
    let pkae_log = fst s in
    match DM.sel sk_log receiver_pk with
    | None ->
      raise
    | Some sk ->
      let option_p = pkaes.dec c sender_pk sk nonce in
      return option_p

let pkae1_dec n pkaes : pkae_dec_t n pkaes =
  fun (sender_pk, receiver_pk, nonce, c) ->
    s <-- get;
    let sk_log:skey_log n = snd s in
    let pkae_log = fst s in
    match DM.sel sk_log receiver_pk with
    | None ->
      raise
    | Some sk ->
      let h =
        if int_of_bytes sender_pk <= int_of_bytes receiver_pk then
          (sender_pk,receiver_pk)
        else
          (receiver_pk,sender_pk)
      in
      match DM.sel #(pkae_log_key) #(pkae_log_value n pkaes) pkae_log (h,nonce) with
      | Some (c',p) ->
        if c = c' then
          return (Some p)
        else
          return None
      | None ->
        return None

type pkae_labels =
    | GEN
    | ENC
    | DEC

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 1"
let pkae_field_types n pkaes : pkae_labels -> Type =
    function  GEN -> pkae_gen_t n pkaes
            | ENC -> pkae_enc_t n pkaes
            | DEC -> pkae_dec_t n pkaes

let pkae_field_rels n pkaes : (l:pkae_labels -> erel (pkae_field_types n pkaes l)) =
  function
      GEN ->
      arrow
        (lo unit)
        (eff_rel (hi (pkae_log n pkaes) ** lo (skey_log n)) (lo (pkey n)))
    | ENC ->
      arrow
        (pkae_enc_inputs n pkaes)
        (eff_rel (pkae_state_rel n pkaes) (lo bytes))
    | DEC ->
      arrow
        (pkae_dec_inputs n pkaes)
        (eff_rel (pkae_state_rel n pkaes) (option_rel (lo (p:bytes{len p `lte` pkaes.max_plaintext_length}))))

let pkae_sig (n:u32) (pkaes:pkae_scheme n) = {
    labels = pkae_labels;
    ops = pkae_field_types n pkaes;
    rels = pkae_field_rels n pkaes
  }

let pkae0_module (n:u32) (pkaes:pkae_scheme n) : module_t (pkae_sig n pkaes) =
  DM.create #_ #(pkae_sig n pkaes).ops
    (function GEN -> pkae_gen n pkaes
            | ENC -> pkae0_enc n pkaes
            | DEC -> pkae0_dec n pkaes)

let pkae1_module (n:u32) (pkaes:pkae_scheme n) : module_t (pkae_sig n pkaes) =
  DM.create #_ #(pkae_sig n pkaes).ops
    (function GEN -> pkae_gen n pkaes
            | ENC -> pkae1_enc n pkaes
            | DEC -> pkae1_dec n pkaes)

let pkae0_functor (n:u32) (pkaes:pkae_scheme n)
  : functor_t (sig_unit) (pkae_sig n pkaes)
  = fun _ ->
      pkae0_module n pkaes

let pkae1_functor (n:u32) (pkaes:pkae_scheme n)
  : functor_t (sig_unit) (pkae_sig n pkaes)
  = fun _ ->
      pkae1_module n pkaes
