module Setoids.Crypto.Proof
open FStar.Bytes
open FStar.UInt32
open FStar.Map
open Setoids
open Setoids.Crypto
open Setoids.Crypto.KEY
open Setoids.Crypto.AE
open Setoids.Crypto.ODH

module DM = FStar.DependentMap
module MONPKAE = Setoids.Crypto.PKAE

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 0"
let pkey n = share n
let nonce = bytes

let pkae_gen_spec n os aes : eff (lo unit) (lo (lbytes32 n) ** lo (lbytes32 n))=
  sk <-- sample_multiple #unit #(lo unit) n;
  let pk = os.exponentiate os.generator sk in
  return (pk,sk)

let pkae_enc_spec n (os:odh_scheme n) (aes:ae_scheme n) p pk sk nonce =
  let k = os.exponentiate pk sk in
  aes.enc p k nonce

let pkae_dec_spec n (os:odh_scheme n) (aes:ae_scheme n) c pk sk nonce =
  let k = os.exponentiate pk sk in
  aes.dec c k nonce

let pkaes n (os:odh_scheme n) (aes:ae_scheme n) =
  MONPKAE.PKAES
    aes.max_plaintext_length
    aes.ciphertext_length
    (pkae_gen_spec n os aes)
    (pkae_enc_spec n os aes)
    (pkae_dec_spec n os aes)

let pkae_state n os aes = MONPKAE.pkae_state n (pkaes n os aes) //(ae_log #n aes * odh_state n) * key_state n

let pkae_state_rel n os aes = MONPKAE.pkae_state_rel n (pkaes n os aes)

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 1"
let lift_ae_state #a (#arel:erel a) n os aes (f:eff (lo (ae_log #n aes) ** lo (key_state n)) arel)
  : eff (pkae_state_rel n os aes) arel
  = fun (t, (ae_st, odh_st)) ->
      let key_st : key_state n = Map.const #handle #(option bool) None , Map.const #handle #(option (lbytes32 n)) None in
      match f (t, (ae_st, key_st)) with
      | None, (ae_st', key_st'), t -> None, (ae_st',odh_st), t
      | Some x, (ae_st', key_st'), t -> Some x, (ae_st',odh_st), t

let lift_odh_state #a (#arel:erel a) n os aes (f:eff (lo (odh_state n) ** lo (key_state n)) arel)
  : eff (pkae_state_rel n os aes) arel
  = fun (t, (ae_st, odh_st)) ->
      let key_st : key_state n = Map.const #handle #(option bool) None , Map.const #handle #(option (lbytes32 n)) None in
      match f (t, (odh_st, key_st)) with
      | None, (odh_st', key_st'), t -> None, (ae_st,odh_st'), t
      | Some x, (odh_st', key_st'), t -> Some x, (ae_st,odh_st'), t

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 0"
let ae_odh_sig n aes = sig_prod (odh_sig n) (ae_sig n aes)
let ae_odh_module n aes = module_t (ae_odh_sig n aes)

//let pkae_gen_t n aes =
//  (lo unit)
//    ^--> eff_rel (((hi (ae_log #n aes)) ** (lo (odh_state n))) ** (lo (key_state n))) (lo (share n))

let pkae_gen n os aes (m:ae_odh_module n aes) : MONPKAE.pkae_gen_t n (pkaes n os aes)
  =
  fun _ ->
    let odh_gen : gen_dh_t n = get_oracle m (Inl GEN_DH) in
    lift_odh_state n os aes (odh_gen ())

let pkae_enc_inputs n (aes:ae_scheme n) =
  quatruple_rel
    (lo (pkey n))
    (lo (pkey n))
    (lo nonce)
    (lo (p:bytes{len p `lte` aes.max_plaintext_length}))

//let pkae_enc_t n aes =
//  pkae_enc_inputs n aes
//    ^--> eff_rel (pkae_state_rel n aes) (lo bytes)

let pkae_enc n os aes (m:ae_odh_module n aes) : MONPKAE.pkae_enc_t n (pkaes n os aes) =
  fun (sender_pk, receiver_pk, nonce, p) ->
    let odh_exp : odh_t n = get_oracle m (Inl ODH) in
    let ae_enc : enc_t n aes = get_oracle m (Inr ENC) in
    h <-- lift_odh_state n os aes (odh_exp (sender_pk, receiver_pk));
    c <-- lift_ae_state n os aes (ae_enc (p,nonce,h));
    return #(pkae_state n os aes) #bytes #(pkae_state_rel n os aes) c

let pkae_dec_inputs n (aes:ae_scheme n) =
  quatruple_rel
    (lo (pkey n))
    (lo (pkey n))
    (lo nonce)
    (lo (c:bytes{len c `lte` aes.ciphertext_length aes.max_plaintext_length}))

//let pkae_dec_t n aes =
//  pkae_dec_inputs n aes
//    ^--> eff_rel (pkae_state_rel n aes) (option_rel (lo (p:bytes{len p `lte` aes.max_plaintext_length})))

let pkae_dec n os aes (m:ae_odh_module n aes) : MONPKAE.pkae_dec_t n (pkaes n os aes) =
  fun (sender_pk, receiver_pk, nonce, c) ->
    let odh_exp : odh_t n = get_oracle m (Inl ODH) in
    let ae_dec : dec_t n aes = get_oracle m (Inr DEC) in
    h <-- lift_odh_state n os aes (odh_exp (sender_pk, receiver_pk));
    p <-- lift_ae_state n os aes (ae_dec (c,nonce,h));
    return p

//type pkae_labels =
//    | GEN
//    | ENC
//    | DEC

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 1"
//let pkae_field_types n aes : pkae_labels -> Type =
//    function  GEN -> pkae_gen_t n aes
//            | ENC -> pkae_enc_t n aes
//            | DEC -> pkae_dec_t n aes
//
//let pkae_field_rels n aes : (l:pkae_labels -> erel (pkae_field_types n aes l)) =
//  function
//      GEN ->
//      arrow
//        (lo unit)
//        (eff_rel (((hi (ae_log #n aes)) ** (lo (odh_state n))) ** (lo (key_state n))) (lo (share n)))
//    | ENC ->
//      arrow
//        (pkae_enc_inputs n aes)
//        (eff_rel (pkae_state_rel n aes) (lo bytes))
//    | DEC ->
//      arrow
//        (pkae_dec_inputs n aes)
//        (eff_rel (pkae_state_rel n aes) (option_rel (lo (p:bytes{len p `lte` aes.max_plaintext_length}))))
//
//let pkae_sig (n:u32) (aes:ae_scheme n) = {
//    labels = pkae_labels;
//    ops = pkae_field_types n aes;
//    rels = pkae_field_rels n aes
//  }

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 1"
let pkae_module (n:u32) os (aes:ae_scheme n) (m:ae_odh_module n aes) : module_t (MONPKAE.pkae_sig n (pkaes n os aes)) =
  DM.create #_ #(MONPKAE.pkae_sig n (pkaes n os aes)).ops
    (function MONPKAE.GEN -> pkae_gen n os aes m
            | MONPKAE.ENC -> pkae_enc n os aes m
            | MONPKAE.DEC -> pkae_dec n os aes m)

let pkae_functor (n:u32) os (aes:ae_scheme n)
  : functor_t (sig_prod (odh_sig n) (ae_sig n aes)) (MONPKAE.pkae_sig n (pkaes n os aes))
  = fun (m:module_t (sig_prod (odh_sig n) (ae_sig n aes))) ->
      //pkae_module n aes m
      admit()

///     ID_WRITE
///     -------- o KEY_0
///     ID_READ
let key0_id_composition n
  : functor_t sig_unit (sig_prod (key_write_sig n) (key_read_sig n)) =
  let id_composition =
    functor_prod_shared_sig
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
      (key_write_functor n)
      (key_read_functor n) in
  comp id_composition (KEY.key1_functor n)

///   ODH
///   ----
///   AE_0
let protocol0_composition n aes os
  : functor_t (sig_prod (key_write_sig n) (key_read_sig n)) (sig_prod (odh_sig n) (ae_sig n aes)) =
  functor_prod
    (odh_functor n os)
    (ae0_functor n aes)

///   ODH
///   ----
///   AE_1
let protocol1_composition n aes os
  : functor_t (sig_prod (key_write_sig n) (key_read_sig n)) (sig_prod (odh_sig n) (ae_sig n aes)) =
  functor_prod
    (odh_functor n os)
    (ae1_functor n aes)

///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_0
///         AE_0   ID_READ
let pkae0_composition n aes os
  : functor_t sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) =
    let prot = comp (protocol0_composition n aes os) (key0_id_composition n) in
    comp (pkae_functor n os aes) prot

///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_1
///         AE_0   ID_READ
let pkae_intermediate_composition1 n aes os
  : functor_t sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) =
    let prot = comp (protocol0_composition n aes os) (key1_id_composition n) in
    comp (pkae_functor n os aes) prot

///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_1
///         AE_1   ID_READ
let pkae_intermediate_composition2 n aes os
  : functor_t sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) =
    let prot = comp (protocol1_composition n aes os) (key1_id_composition n) in
    comp (pkae_functor n os aes) prot

///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_0
///         AE_1   ID_READ
let pkae1_composition n aes os
  : functor_t sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) =
    let prot = comp (protocol1_composition n aes os) (key0_id_composition n) in
    comp (pkae_functor n os aes) prot

let pkae_rel n os aes
  : per
    (functor_t
      sig_unit
      (MONPKAE.pkae_sig n (pkaes n os aes)))
  =
  fun
    pkae0
    pkae1
    ->
  let pkae0_module = pkae0 mod_unit in
  let pkae1_module = pkae1 mod_unit in
  sig_rel' (MONPKAE.pkae_sig n (pkaes n os aes)) pkae0_module pkae1_module

/// Proof:
/// Assumptions:
/// ODH o ID_WRITE            ODH o ID_WRITE
/// -------------- o KEY_0 =  -------------- o KEY_1
///    ID_READ                    ID_READ

///    ID_WRITE                     ID_WRITE
/// ---------------- o KEY_1 =  ---------------- o KEY_1
///  AE_0 o ID_READ              AE_1 o ID_READ
///
/// Goal: Show that we can instantiate an eq instance with pkae0 and pkae1
/// Note, that for the full cryptographic proof, we would have to show `Perfect`
/// equivalence with the actual PKAE security notion, which I have not yet
/// encoded. However, that should be trivial, once we have make the following
/// work.

/// First step: pull ODH assumption to the right and make sure the result is
/// still equal. Then idealize ODH and pull it back to the left.
///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_0
///         AE_0   ID_READ
/// to
///         ID_ODH     ODH o ID_WRITE
///  PKAE o ------ o ----------------- o KEY_0
///         AE_0         ID_READ
/// to
///         ID_ODH     ODH o ID_WRITE
///  PKAE o ------ o ----------------- o KEY_1
///         AE_0         ID_READ
/// to
///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_1
///         AE_0   ID_READ
let step1_left_side n os aes =
  comp (pkae_functor n os aes)
       (functor_prod
         id_func
         (ae0_functor n aes))

/// Second step: pull AE assumption to the right and make sure the result is
/// still equal. Then idealize AE and pull it back to the left.
///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_1
///         AE_0   ID_READ
/// to
///         ODH        ID_WRITE
///  PKAE o ---- o ----------------- o KEY_1
///         ID_AE    AE_0 o ID_READ
/// to
///         ODH        ID_WRITE
///  PKAE o ---- o ----------------- o KEY_1
///         ID_AE    AE_1 o ID_READ
/// to
///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_1
///         AE_1   ID_READ
let step2_left_side n os aes =
  comp
    (pkae_functor n os aes)
    (functor_prod (odh_functor n os) id_func)

/// Third step: pull ODH assumption to the right and make sure the result is
/// still equal. Then de-idealize ODH and pull it back to the left.
///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_1
///         AE_1   ID_READ
/// to
///         ID_ODH     ODH o ID_WRITE
///  PKAE o ------ o ----------------- o KEY_1
///         AE_1         ID_READ
/// to
///         ID_ODH     ODH o ID_WRITE
///  PKAE o ------ o ----------------- o KEY_0
///         AE_1         ID_READ
/// to
///         ODH    ID_WRITE
///  PKAE o ---- o -------- o KEY_0
///         AE_1   ID_READ
let step3_left_side n os aes =
  comp (pkae_functor n os aes)
       (functor_prod
         id_func
         (ae1_functor n aes))

let odh_step1_eps n os aes = (eps_trans (step1_left_side n os aes) (odh_eps n))
let ae_step2_eps n os aes = (eps_trans (step2_left_side n os aes) (ae_eps n aes))
let odh_step3_eps n os aes = (eps_trans (step3_left_side n os aes) (odh_eps n))
let eps_sum n os aes = sum (ae_step2_eps n os aes) (odh_step1_eps n os aes)
let eps_sum2 n os aes = sum (eps_sum n os aes) (odh_step3_eps n os aes)

#set-options "--z3rlimit 550 --max_fuel 0 --max_ifuel 0 --query_stats"
let pkae_proof (n:u32) (aes:ae_scheme n) (os:odh_scheme n)
  : eq (pkae_rel n os aes)
       (eps_sum2 n os aes)
       (pkae0_composition n aes os)
       (pkae1_composition n aes os) =
  // Prove here, that pulling ODH to the right doesn't change anything.
  let step1a_eq
  : eq
    (pkae_rel n os aes)
    (eps_z)
    (pkae0_composition n aes os)
    (comp
      (step1_left_side n os aes)
      (odh_game0 n os))
    =
    Perfect #_ #_ #(pkae_rel n os aes)
      (pkae0_composition n aes os)
      (comp
        (step1_left_side n os aes)
        (odh_game0 n os))
      ()
  in
  // Redefining this seems necessary for F* to be able to assert equivalence of the epsilons.
  let odh_step1_eps : eps sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) = odh_step1_eps n os aes in
  let ae_step2_eps : eps sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) = ae_step2_eps n os aes in
  let odh_step3_eps : eps sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) = odh_step3_eps n os aes in
  let eps_sum : eps sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) = eps_sum n os aes in
  let eps_sum2 : eps sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) = eps_sum2 n os aes in
  // Now apply the ODH assumption via the Ctx rule.
  let step1b_eq
  : eq
    (pkae_rel n os aes)
    odh_step1_eps
    (pkae0_composition n aes os)
    (comp
      (step1_left_side n os aes)
      (odh_game1 n os))
    =
    Trans
      step1a_eq
      (Ctx #_ #_ #(pkae_rel n os aes)
        (odh_assumption n os)
        (step1_left_side n os aes))
  in
  // Finish the first step by pulling ODH to the left again. Note, that the KEY package is now idealized (KEY_0 -> KEY_1)
  // and prove again, that nothing changes by pulling ODH back to the left (now with KEY_1 instead of KEY_0).
  let step1_final_eq
  : eq
    (pkae_rel n os aes)
    (odh_step1_eps)
    (pkae0_composition n aes os)
    (pkae_intermediate_composition1 n aes os)
  =
    Trans
      step1b_eq
      (Perfect #_ #_ #(pkae_rel n os aes)
        (comp
          (step1_left_side n os aes)
          (odh_game1 n os))
        (pkae_intermediate_composition1 n aes os)
        ())
  in
  let step2a_eq
  : eq
    (pkae_rel n os aes)
    (odh_step1_eps)
    (pkae0_composition n aes os)
    (comp
      (step2_left_side n os aes)
      (ae_game0 n aes))
  =
    Trans
      step1_final_eq
      (Perfect #_ #_ #(pkae_rel n os aes)
        (pkae_intermediate_composition1 n aes os)
        (comp
          (step2_left_side n os aes)
          (ae_game0 n aes))
        ())
  in
  // Now apply the AE assumption via the Ctx rule.
  let step2b_eq
  : eq
    (pkae_rel n os aes)
    (eps_sum)
    (pkae0_composition n aes os)
    (comp
      (step2_left_side n os aes)
      (ae_game1 n aes))
  =
    Trans
      step2a_eq
      (Ctx #_ #_ #(pkae_rel n os aes)
        (ae_assumption n aes)
        (step2_left_side n os aes))
  in
  // Finish the first step by pulling ODH to the left again. Note, that the KEY package is now idealized (KEY_0 -> KEY_1)
  // and prove again, that nothing changes by pulling ODH back to the left (now with KEY_1 instead of KEY_0).
  let step2_final_eq
  : eq
    (pkae_rel n os aes)
    (eps_sum)
    (pkae0_composition n aes os)
    (pkae_intermediate_composition2 n aes os)
  =
  Trans
    step2b_eq
    (Perfect #_ #_ #(pkae_rel n os aes)
      (comp
        (step2_left_side n os aes)
        (ae_game1 n aes))
      (pkae_intermediate_composition2 n aes os)
      ())
  in
  // Now, repeat step 1, i.e. pull ODH to the right, apply the assumption and pull it back to the left.
  // Prove here, that pulling ODH to the right doesn't change anything.
  let step3a_eq
  : eq
    (pkae_rel n os aes)
    (eps_sum)
    (pkae0_composition n aes os)
    (comp
      (step3_left_side n os aes)
      (odh_game1 n os))
    =
    Trans
      step2_final_eq
      (Perfect #_ #_ #(pkae_rel n os aes)
        (pkae_intermediate_composition2 n aes os)
        (comp
          (step3_left_side n os aes)
          (odh_game1 n os))
        ())
  in
  // Redefining this seems necessary for F* to be able to assert equivalence of the epsilons.
  //let odh_step_eps : eps sig_unit (MONPKAE.pkae_sig n (pkaes n os aes)) = odh_step_eps n os aes in
  // Now apply the ODH assumption via the Ctx rule.
  let step3b_eq
  : eq
    (pkae_rel n os aes)
    (eps_sum2)
    (pkae0_composition n aes os)
    (comp
      (step3_left_side n os aes)
      (odh_game0 n os))
    =
    Trans
      step3a_eq
      (Ctx #_ #_ #(pkae_rel n os aes)
        (Sym (odh_assumption n os))
        (step3_left_side n os aes))
  in
  // Finish the first step by pulling ODH to the left again. Note, that the KEY package is now idealized (KEY_0 -> KEY_1)
  // and prove again, that nothing changes by pulling ODH back to the left (now with KEY_1 instead of KEY_0).
  Trans
    step3b_eq
    (Perfect #_ #_ #(pkae_rel n os aes)
      (comp
        (step3_left_side n os aes)
        (odh_game0 n os))
      (pkae1_composition n aes os)
      ())

/// Equivalence proof of Mod-PKAE and Mon-PKAE

let pkae_gen_eq n os aes =
  let prot = comp (protocol0_composition n aes os) (key0_id_composition n) in
  let m = prot mod_unit in
  squash
    (pkae_gen n os aes m
      `arrow
        (lo unit)
        (eff_rel (((hi (ae_log #n aes)) ** (lo (odh_state n)))) (lo (share n)))`
    MONPKAE.pkae_gen n (pkaes n os aes)
    )

let test n os aes : pkae_gen_eq n os aes = ()

let pkae_enc_eq n os aes =
  let prot = comp (protocol0_composition n aes os) (key0_id_composition n) in
  let m = prot mod_unit in
  squash
    (pkae_enc n os aes m
      `arrow
        (pkae_enc_inputs n aes)
        (eff_rel (pkae_state_rel n os aes) (lo bytes))`
    MONPKAE.pkae0_enc n (pkaes n os aes)
    )

let pkae_dec_eq n os aes =
  let prot = comp (protocol0_composition n aes os) (key0_id_composition n) in
  let m = prot mod_unit in
  squash(pkae_dec n os aes m
    `arrow
      (pkae_dec_inputs n aes)
      (eff_rel (pkae_state_rel n os aes) (option_rel (lo (p:bytes{len p `lte` aes.max_plaintext_length}))))`
  MONPKAE.pkae0_dec n (pkaes n os aes)
  )//;
  //squash
  //  (DM.sel m MONPKAE.DEC
  //  `(MONPKAE.pkae_sig n (pkaes n os aes)).rels MONPKAE.DEC`
  //  DM.sel (MONPKAE.pkae0_module n (pkaes n os aes)) MONPKAE.DEC)


let pkae_eq_proof (n:u32) (aes:ae_scheme n) (os:odh_scheme n)
  //: eq (pkae_rel n os aes)
  //     (eps_z)
  //     (pkae0_composition n aes os)
  //     (MONPKAE.pkae0_functor n (pkaes n os aes))
  =
    Perfect #_ #_ #(pkae_rel n os aes) (pkae0_composition n aes os) (MONPKAE.pkae0_functor n (pkaes n os aes)) (
      pkae_gen_eq n os aes /\
      pkae_enc_eq n os aes /\
      pkae_dec_eq n os aes
    )
