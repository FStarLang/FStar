module DPETypes
open Pulse.Lib.Pervasives
open HACL
open X509
open EngineTypes
open EngineCore
open L0Types
open L0Core
module L = Pulse.Lib.SpinLock
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT

(* Profile Descriptor *)
type profile_descriptor_t = {
  name: string;
  dpe_spec_version: U32.t;
  max_message_size: U32.t;
  uses_multi_part_messages: bool;
  supports_concurrent_operations: bool;
  supports_encrypted_sessions: bool;
  supports_derived_sessions: bool;
  max_sessions: SZ.t;
  session_protocol: string;
  supports_session_sync: bool;
  session_sync_policy: string;
  session_migration_protocol: string;
  supports_default_context: bool;
  supports_context_handles: bool;
  max_contexts_per_session: SZ.t;
  max_context_handle_size: SZ.t;
  supports_auto_init: bool;
  supports_simulation: bool;
  supports_attestation: bool;
  supports_sealing: bool;
  supports_get_profile: bool;
  supports_open_session: bool;
  supports_close_session: bool;
  supports_sync_session: bool;
  supports_export_session: bool;
  supports_import_session: bool;
  supports_init_context: bool;
  supports_certify_key: bool;
  supports_sign: bool;
  supports_seal: bool;
  supports_unseal: bool;
  supports_sealing_public: bool;
  supports_rotate_context_handle: bool;
  dice_derivation: string;
  asymmetric_derivation: string;
  symmetric_derivation: string;
  supports_any_label: bool;
  supported_labels: string;
  initial_derivation: string;
  input_format: string;
  supports_internal_inputs: bool;
  supports_internal_dpe_info: bool;
  supports_internal_dpe_dice: bool;
  internal_dpe_info_type: string;
  internal_dpe_dice_type: string;
  internal_inputs: string;
  supports_certificates: bool;
  max_certificate_size: SZ.t;
  max_certificate_chain_size: SZ.t;
  appends_more_certificates: bool;
  supports_certificate_policies: bool;
  supports_policy_identity_init: bool;
  supports_policy_identity_loc: bool;
  supports_policy_attest_init: bool;
  supports_policy_attest_loc: bool;
  supports_policy_assert_init: bool;
  supports_policy_assert_loc: bool;
  certificate_policies: string;
  supports_eca_certificates: bool;
  eca_certificate_format: string;
  leaf_certificate_format: string;
  public_key_format: string;
  supports_external_key: bool;
  to_be_signed_format: string;
  signature_format: string;
  supports_symmetric_sign: bool;
  supports_asymmetric_unseal: bool;
  supports_unseal_policy: bool;
  unseal_policy_format: string;
}

let mk_profile_descriptor 
  name dpe_spec_version max_message_size uses_multi_part_messages
  supports_concurrent_operations supports_encrypted_sessions supports_derived_sessions
  max_sessions session_protocol supports_session_sync session_sync_policy
  session_migration_protocol supports_default_context supports_context_handles
  max_contexts_per_session max_context_handle_size supports_auto_init
  supports_simulation supports_attestation supports_sealing supports_get_profile
  supports_open_session supports_close_session supports_sync_session
  supports_export_session supports_import_session supports_init_context
  supports_certify_key supports_sign supports_seal supports_unseal 
  supports_sealing_public supports_rotate_context_handle dice_derivation
  asymmetric_derivation symmetric_derivation supports_any_label supported_labels
  initial_derivation input_format supports_internal_inputs supports_internal_dpe_info
  supports_internal_dpe_dice internal_dpe_info_type internal_dpe_dice_type
  internal_inputs supports_certificates max_certificate_size max_certificate_chain_size
  appends_more_certificates supports_certificate_policies supports_policy_identity_init 
  supports_policy_identity_loc supports_policy_attest_init supports_policy_attest_loc 
  supports_policy_assert_init supports_policy_assert_loc certificate_policies 
  supports_eca_certificates eca_certificate_format leaf_certificate_format public_key_format 
  supports_external_key to_be_signed_format signature_format supports_symmetric_sign 
  supports_asymmetric_unseal supports_unseal_policy unseal_policy_format
: profile_descriptor_t
= {name; dpe_spec_version; max_message_size; uses_multi_part_messages;
  supports_concurrent_operations; supports_encrypted_sessions; supports_derived_sessions;
  max_sessions; session_protocol; supports_session_sync; session_sync_policy;
  session_migration_protocol; supports_default_context; supports_context_handles;
  max_contexts_per_session; max_context_handle_size; supports_auto_init;
  supports_simulation; supports_attestation; supports_sealing; supports_get_profile;
  supports_open_session; supports_close_session; supports_sync_session;
  supports_export_session; supports_import_session; supports_init_context;
  supports_certify_key; supports_sign; supports_seal; supports_unseal; 
  supports_sealing_public; supports_rotate_context_handle; dice_derivation;
  asymmetric_derivation; symmetric_derivation; supports_any_label; supported_labels;
  initial_derivation; input_format; supports_internal_inputs; supports_internal_dpe_info;
  supports_internal_dpe_dice; internal_dpe_info_type; internal_dpe_dice_type;
  internal_inputs; supports_certificates; max_certificate_size; max_certificate_chain_size; 
  appends_more_certificates; supports_certificate_policies; supports_policy_identity_init; 
  supports_policy_identity_loc; supports_policy_attest_init; supports_policy_attest_loc; 
  supports_policy_assert_init; supports_policy_assert_loc; certificate_policies; 
  supports_eca_certificates; eca_certificate_format; leaf_certificate_format; public_key_format; 
  supports_external_key; to_be_signed_format; signature_format; supports_symmetric_sign; 
  supports_asymmetric_unseal; supports_unseal_policy; unseal_policy_format;}

(* Engine Context *)
noeq
type engine_context_t = { 
  uds: A.larray U8.t (SZ.v uds_len); 
}

let engine_context_perm (c:engine_context_t) : vprop
  = A.pts_to c.uds full_perm uds_bytes ** 
    pure (A.is_full_array c.uds)

let mk_engine_context_t uds : engine_context_t = {uds}

(* L0 Context *)
noeq
type l0_context_t = { 
  cdi:A.larray U8.t (SZ.v dice_digest_len); 
}

let mk_l0_context_t cdi : l0_context_t = {cdi}

type l0_context_repr_t = {
  cdi:elseq U8.t dice_digest_len;
  repr:engine_record_repr;
}

let mk_l0_context_repr_t
  (cdi:erased (elseq U8.t dice_digest_len)) 
  (repr:erased engine_record_repr) 
: erased l0_context_repr_t 
= {cdi; repr}

let l0_context_perm (c:l0_context_t) (r:l0_context_repr_t): vprop
  = A.pts_to c.cdi full_perm r.cdi **
    pure (A.is_full_array c.cdi
       /\ cdi_functional_correctness r.cdi r.repr
       /\ l0_is_authentic r.repr)


(* L1 Context *)
noeq
type l1_context_t = { deviceID_priv: A.larray U8.t (SZ.v v32us);
                    deviceID_pub: A.larray U8.t (SZ.v v32us);   
                    aliasKey_priv: A.larray U8.t (SZ.v v32us);
                    aliasKey_pub: A.larray U8.t (SZ.v v32us);
                    aliasKeyCRT: A.array U8.t;
                    deviceIDCSR: A.array U8.t; }

let mk_l1_context_t deviceID_priv deviceID_pub aliasKey_priv aliasKey_pub aliasKeyCRT deviceIDCSR 
: l1_context_t
= { deviceID_priv; deviceID_pub; aliasKey_priv; aliasKey_pub; aliasKeyCRT; deviceIDCSR }

noeq
type l1_context_repr_t = {
  deviceID_label_len: hkdf_lbl_len;
  aliasKey_label_len: hkdf_lbl_len;
  deviceID_priv: elseq U8.t v32us;
  deviceID_pub: elseq U8.t v32us;
  aliasKey_priv: elseq U8.t v32us;
  aliasKey_pub:elseq U8.t v32us;
  aliasKeyCRT_len:SZ.t;
  aliasKeyCRT: elseq U8.t aliasKeyCRT_len;
  deviceIDCSR_len:SZ.t;
  deviceIDCSR:elseq U8.t deviceIDCSR_len;
  cdi:elseq U8.t dice_digest_len;
  repr:l0_record_repr;
  deviceIDCSR_ingredients: deviceIDCSR_ingredients_t;
  aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t;
}

let mk_l1_context_repr_t 
  (deviceID_label_len:erased hkdf_lbl_len)
  (aliasKey_label_len:erased hkdf_lbl_len)
  (deviceID_priv:erased (elseq U8.t v32us))
  (deviceID_pub:erased (elseq U8.t v32us))
  (aliasKey_priv:erased (elseq U8.t v32us))
  (aliasKey_pub:erased (elseq U8.t v32us))
  (aliasKeyCRT_len:erased SZ.t)
  (aliasKeyCRT:erased (elseq U8.t aliasKeyCRT_len))
  (deviceIDCSR_len:erased SZ.t)
  (deviceIDCSR:erased (elseq U8.t deviceIDCSR_len))
  (cdi:erased (elseq U8.t dice_digest_len))
  (repr:erased l0_record_repr)
  (deviceIDCSR_ingredients:erased deviceIDCSR_ingredients_t)
  (aliasKeyCRT_ingredients:erased aliasKeyCRT_ingredients_t)
: erased l1_context_repr_t 
= {deviceID_label_len; aliasKey_label_len; deviceID_priv; deviceID_pub; aliasKey_priv;
  aliasKey_pub; aliasKeyCRT_len; aliasKeyCRT; deviceIDCSR_len; deviceIDCSR;
  cdi; repr; deviceIDCSR_ingredients; aliasKeyCRT_ingredients}

let l1_context_perm (c:l1_context_t) (r:l1_context_repr_t)
  : vprop
  = A.pts_to c.deviceID_priv full_perm r.deviceID_priv **
    A.pts_to c.deviceID_pub full_perm r.deviceID_pub **
    A.pts_to c.aliasKey_priv full_perm r.aliasKey_priv **
    A.pts_to c.aliasKey_pub full_perm r.aliasKey_pub **
    A.pts_to c.aliasKeyCRT full_perm r.aliasKeyCRT **
    A.pts_to c.deviceIDCSR full_perm r.deviceIDCSR **
    pure (
      valid_hkdf_ikm_len dice_digest_len /\
      aliasKey_functional_correctness
        dice_hash_alg dice_digest_len r.cdi r.repr.fwid
        r.aliasKey_label_len r.repr.aliasKey_label 
        r.aliasKey_pub r.aliasKey_priv /\
      deviceIDCSR_functional_correctness 
        dice_hash_alg dice_digest_len r.cdi
        r.deviceID_label_len r.repr.deviceID_label r.deviceIDCSR_ingredients 
        r.deviceIDCSR_len r.deviceIDCSR /\       
      aliasKeyCRT_functional_correctness 
        dice_hash_alg dice_digest_len r.cdi r.repr.fwid
        r.deviceID_label_len r.repr.deviceID_label r.aliasKeyCRT_ingredients 
        r.aliasKeyCRT_len r.aliasKeyCRT r.aliasKey_pub /\
      A.is_full_array c.deviceID_priv /\
      A.is_full_array c.deviceID_pub /\
      A.is_full_array c.aliasKey_priv /\
      A.is_full_array c.aliasKey_pub /\
      A.is_full_array c.aliasKeyCRT /\
      A.is_full_array c.deviceIDCSR
    )  

(* Generic Context *)    // this is called an enumeration
noeq
type context_t = 
  | Engine_context : c:engine_context_t -> context_t
  | L0_context     : c:l0_context_t -> context_t
  | L1_context     : c:l1_context_t -> context_t

let mk_context_t_engine c = Engine_context c
let mk_context_t_l0 c = L0_context c
let mk_context_t_l1 c = L1_context c

noeq
type context_repr_t = 
  | Engine_context_repr : context_repr_t
  | L0_context_repr     : r:l0_context_repr_t -> context_repr_t
  | L1_context_repr     : r:l1_context_repr_t -> context_repr_t

let mk_context_repr_t_l0 (r:erased l0_context_repr_t) 
: erased context_repr_t = L0_context_repr r
let mk_context_repr_t_l1 (r:erased l1_context_repr_t) 
: erased context_repr_t = L1_context_repr r

let context_perm (context:context_t) (repr:context_repr_t): vprop = 
  match context with
  | Engine_context c -> engine_context_perm c
  | L0_context c -> (
    match repr with 
    | L0_context_repr r -> l0_context_perm c r
    | _ -> pure False
  )
  | L1_context c -> (
    match repr with
    | L1_context_repr r -> l1_context_perm c r
    | _ -> pure False
  )

val get_l0_context_perm (context:context_t{L0_context? context}) (repr:erased context_repr_t)
  : stt_ghost (erased l0_context_repr_t) emp_inames
              (context_perm context repr)
              (fun r -> l0_context_perm (L0_context?.c context) r
                      ** pure(reveal repr == L0_context_repr r))

val get_l1_context_perm (context:context_t{L1_context? context}) (repr:erased context_repr_t)
  : stt_ghost (erased l1_context_repr_t) emp_inames
              (context_perm context repr)
              (fun r -> l1_context_perm (L1_context?.c context) r
                      ** pure(reveal repr == L1_context_repr r))

// In the implmentation, we store contexts as values in a global hash table
// so we need a way to store and retrieve permission on the context. We do this
// by keeping a tuple of the context along with a lock on the context permission
let locked_context_t = c:context_t 
                     & r:erased context_repr_t 
                     & L.lock (context_perm c r)

(* Record *)
noeq
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t

noeq
type repr_t = 
  | Engine_repr : r:engine_record_repr -> repr_t
  | L0_repr     : r:l0_record_repr -> repr_t

let record_perm (record:record_t) (repr:repr_t) : vprop = 
  match record with
  | Engine_record r -> (
    match repr with 
    | Engine_repr r0 -> engine_record_perm r r0
    | _ -> pure False
  )
  | L0_record r -> (
    match repr with
    | L0_repr r0 -> l0_record_perm r r0
    | _ -> pure False
  )

```pulse
ghost
fn elim_false (#a:Type0) (p: (a -> vprop))
    requires pure False
    returns x:a
    ensures p x
{
    let x = false_elim #a ();
    rewrite emp as (p x);
    x
}
```
// ```pulse
// ghost
// fn get_engine_record_perm_ (r:engine_record_t) (repr:repr_t)
//   requires record_perm (Engine_record r) repr
//   returns r0:engine_record_repr
//   ensures engine_record_perm r r0 ** pure (repr == Engine_repr r0)
// {
//    match repr {
//     Engine_repr r0 -> {
//       rewrite (record_perm (Engine_record r) repr)
//           as  (engine_record_perm r r0);
//       r0
//     }
//     _ -> {
//       rewrite (record_perm (Engine_record r) repr)
//           as  (pure False);
//       elim_false (engine_record_perm r)
//     }
//   }
// }
// ```
// ```pulse
// ghost
// fn get_engine_record_perm (r:engine_record_t) (repr:erased repr_t)
//   requires record_perm (Engine_record r) repr
//   returns r0:erased engine_record_repr
//   ensures engine_record_perm r r0 ** pure (reveal repr == Engine_repr r0)
// {
//   let r = get_engine_record_perm_ r repr;
//   hide r
// }
// ```

val get_engine_record_perm (record:record_t{Engine_record? record}) (repr:erased repr_t)
  : stt_ghost (erased engine_record_repr) emp_inames
              (record_perm record repr)
              (fun r0 -> engine_record_perm (Engine_record?.r record) r0 
                      ** pure(reveal repr == Engine_repr r0))

val get_l0_record_perm (record:record_t{L0_record? record}) (repr:erased repr_t)
  : stt_ghost (erased l0_record_repr) emp_inames
              (record_perm record repr)
              (fun r0 -> l0_record_perm (L0_record?.r record) r0 
                      ** pure(reveal repr == L0_repr r0))
