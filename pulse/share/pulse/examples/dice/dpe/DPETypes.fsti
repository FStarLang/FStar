(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module DPETypes
#lang-pulse
open Pulse.Lib.Pervasives
open HACL
open EngineTypes
open EngineCore
open L0Types
open L0Core
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
  name dpe_spec_version max_message_size uses_multi_part_messages supports_concurrent_operations supports_encrypted_sessions supports_derived_sessions
  max_sessions session_protocol supports_session_sync session_sync_policy session_migration_protocol supports_default_context supports_context_handles
  max_contexts_per_session max_context_handle_size supports_auto_init supports_simulation supports_attestation supports_sealing supports_get_profile
  supports_open_session supports_close_session supports_sync_session supports_export_session supports_import_session supports_init_context
  supports_certify_key supports_sign supports_seal supports_unseal  supports_sealing_public supports_rotate_context_handle dice_derivation
  asymmetric_derivation symmetric_derivation supports_any_label supported_labels initial_derivation input_format supports_internal_inputs supports_internal_dpe_info
  supports_internal_dpe_dice internal_dpe_info_type internal_dpe_dice_type internal_inputs supports_certificates max_certificate_size max_certificate_chain_size
  appends_more_certificates supports_certificate_policies supports_policy_identity_init supports_policy_identity_loc supports_policy_attest_init supports_policy_attest_loc 
  supports_policy_assert_init supports_policy_assert_loc certificate_policies supports_eca_certificates eca_certificate_format leaf_certificate_format public_key_format 
  supports_external_key to_be_signed_format signature_format supports_symmetric_sign supports_asymmetric_unseal supports_unseal_policy unseal_policy_format
: profile_descriptor_t
= {name; dpe_spec_version; max_message_size; uses_multi_part_messages; supports_concurrent_operations; supports_encrypted_sessions; supports_derived_sessions;
  max_sessions; session_protocol; supports_session_sync; session_sync_policy; session_migration_protocol; supports_default_context; supports_context_handles;
  max_contexts_per_session; max_context_handle_size; supports_auto_init; supports_simulation; supports_attestation; supports_sealing; supports_get_profile;
  supports_open_session; supports_close_session; supports_sync_session; supports_export_session; supports_import_session; supports_init_context;
  supports_certify_key; supports_sign; supports_seal; supports_unseal; supports_sealing_public; supports_rotate_context_handle; dice_derivation;
  asymmetric_derivation; symmetric_derivation; supports_any_label; supported_labels; initial_derivation; input_format; supports_internal_inputs; supports_internal_dpe_info;
  supports_internal_dpe_dice; internal_dpe_info_type; internal_dpe_dice_type; internal_inputs; supports_certificates; max_certificate_size; max_certificate_chain_size; 
  appends_more_certificates; supports_certificate_policies; supports_policy_identity_init; supports_policy_identity_loc; supports_policy_attest_init; supports_policy_attest_loc; 
  supports_policy_assert_init; supports_policy_assert_loc; certificate_policies; supports_eca_certificates; eca_certificate_format; leaf_certificate_format; public_key_format; 
  supports_external_key; to_be_signed_format; signature_format; supports_symmetric_sign; supports_asymmetric_unseal; supports_unseal_policy; unseal_policy_format;}

module V = Pulse.Lib.Vec

(* Engine Context *)
[@@ Rust_derive "Clone"]
noeq
type engine_context_t = { 
  uds: V.lvec U8.t (SZ.v uds_len); 
}

let engine_context_perm (c:engine_context_t) (uds_bytes:Seq.seq U8.t) : slprop
  = pts_to c.uds uds_bytes ** 
    pure (V.is_full_vec c.uds)

let mk_engine_context_t uds : engine_context_t = {uds}

(* L0 Context *)
[@@ Rust_derive "Clone"]
noeq
type l0_context_t = { 
  cdi : V.lvec U8.t (SZ.v dice_digest_len); 
}

let mk_l0_context_t cdi : l0_context_t = {cdi}

type l0_context_repr_t = {
  uds:Seq.seq U8.t;
  cdi:Seq.seq U8.t;
  repr:(repr:engine_record_repr {
    cdi_functional_correctness cdi uds repr /\
    l0_is_authentic repr });
}

let mk_l0_context_repr_t
  (uds:Seq.seq U8.t)
  (cdi:Seq.seq U8.t)
  (repr:engine_record_repr {
    cdi_functional_correctness cdi uds repr /\
    l0_is_authentic repr })
: GTot l0_context_repr_t 
= {uds; cdi; repr}

let l0_context_perm ([@@@mkey] c:l0_context_t) (r:l0_context_repr_t): slprop
  = pts_to c.cdi r.cdi **
    pure (V.is_full_vec c.cdi)

(* L1 Context *)
[@@ Rust_derive "Clone"]
noeq
type l1_context_t = {
  deviceID_pub: V.lvec U8.t 32;
  aliasKey_priv: V.lvec U8.t 32;
  aliasKey_pub: V.lvec U8.t 32;
  deviceIDCSR_len : U32.t;
  deviceIDCSR: V.lvec U8.t (U32.v deviceIDCSR_len);
  aliasKeyCRT_len : U32.t;
  aliasKeyCRT: V.lvec U8.t (U32.v aliasKeyCRT_len);
}

let mk_l1_context_t deviceID_pub aliasKey_pub aliasKey_priv deviceIDCSR_len deviceIDCSR aliasKeyCRT_len aliasKeyCRT
: l1_context_t
= {deviceID_pub; aliasKey_pub; aliasKey_priv; deviceIDCSR_len; deviceIDCSR; aliasKeyCRT_len; aliasKeyCRT}

noeq
type l1_context_repr_t = {
  cdi:Seq.seq U8.t;
  deviceID_label_len:(n:U32.t { valid_hkdf_lbl_len n });
  aliasKey_label_len:(n:U32.t { valid_hkdf_lbl_len n });
  deviceIDCSR_ingredients:deviceIDCSR_ingredients_t;
  aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t;
  deviceID_pub:Seq.seq U8.t;
  aliasKey_pub:Seq.seq U8.t;
  aliasKey_priv:Seq.seq U8.t;
  deviceIDCSR_len:(n:U32.t { valid_deviceIDCSR_ingredients deviceIDCSR_ingredients n });
  deviceIDCSR:Seq.seq U8.t;
  aliasKeyCRT_len:(n:U32.t { valid_aliasKeyCRT_ingredients aliasKeyCRT_ingredients n });
  aliasKeyCRT:Seq.seq U8.t;
  repr:(repr:l0_record_repr_t {
    l0_post
     cdi
     repr.fwid
     deviceID_label_len
     repr.deviceID_label
     aliasKey_label_len
     repr.aliasKey_label
     deviceIDCSR_ingredients
     aliasKeyCRT_ingredients
     deviceID_pub
     aliasKey_pub
     aliasKey_priv
     deviceIDCSR_len
     deviceIDCSR
     aliasKeyCRT_len
     aliasKeyCRT
  });
}

let mk_l1_context_repr_t
  (cdi:Seq.seq U8.t)
  (deviceID_label_len:(n:U32.t { valid_hkdf_lbl_len n }))
  (aliasKey_label_len:(n:U32.t { valid_hkdf_lbl_len n }))
  (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (deviceID_pub:Seq.seq U8.t)
  (aliasKey_pub:Seq.seq U8.t)
  (aliasKey_priv:Seq.seq U8.t)
  (deviceIDCSR_len:(n:U32.t { valid_deviceIDCSR_ingredients deviceIDCSR_ingredients n }))
  (deviceIDCSR:Seq.seq U8.t)
  (aliasKeyCRT_len:(n:U32.t { valid_aliasKeyCRT_ingredients aliasKeyCRT_ingredients n }))
  (aliasKeyCRT:Seq.seq U8.t)
  (repr:(repr:l0_record_repr_t {
     l0_post
       cdi
       repr.fwid
       deviceID_label_len
       repr.deviceID_label
       aliasKey_label_len
       repr.aliasKey_label
       deviceIDCSR_ingredients
       aliasKeyCRT_ingredients
       deviceID_pub
       aliasKey_pub
       aliasKey_priv
       deviceIDCSR_len
       deviceIDCSR
       aliasKeyCRT_len
       aliasKeyCRT }))
  : GTot l1_context_repr_t =
  { cdi; deviceID_label_len; aliasKey_label_len; deviceIDCSR_ingredients; aliasKeyCRT_ingredients;
    deviceID_pub; aliasKey_pub; aliasKey_priv; deviceIDCSR_len; deviceIDCSR; aliasKeyCRT_len; aliasKeyCRT; repr }

let l1_context_perm ([@@@mkey] c:l1_context_t) (r:l1_context_repr_t)
  : slprop
  = pts_to c.deviceID_pub r.deviceID_pub **
    pts_to c.aliasKey_pub r.aliasKey_pub **
    pts_to c.aliasKey_priv r.aliasKey_priv **
    pts_to c.deviceIDCSR r.deviceIDCSR **
    pts_to c.aliasKeyCRT r.aliasKeyCRT **
    pure (V.is_full_vec c.deviceID_pub /\
          V.is_full_vec c.aliasKey_pub /\
          V.is_full_vec c.aliasKey_priv /\
          V.is_full_vec c.deviceIDCSR /\
          V.is_full_vec c.aliasKeyCRT)

[@@ Rust_derive "Clone"]
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
  | Engine_context_repr : uds:Seq.seq U8.t -> context_repr_t
  | L0_context_repr     : r:l0_context_repr_t -> context_repr_t
  | L1_context_repr     : r:l1_context_repr_t -> context_repr_t

let mk_context_repr_t_l0 (r:erased l0_context_repr_t) 
: erased context_repr_t = L0_context_repr r
let mk_context_repr_t_l1 (r:erased l1_context_repr_t) 
: erased context_repr_t = L1_context_repr r

let context_perm ([@@@mkey] context:context_t) (repr:context_repr_t): slprop = 
  match context, repr with
  | Engine_context c, Engine_context_repr uds -> engine_context_perm c uds
  | L0_context c, L0_context_repr r -> l0_context_perm c r
  | L1_context c, L1_context_repr r -> l1_context_perm c r
  | _ -> pure False

let context_and_repr_tag_related (c:context_t) (r:context_repr_t) : bool =
  match c, r with
  | Engine_context _, Engine_context_repr _
  | L0_context _, L0_context_repr _
  | L1_context _, L1_context_repr _ -> true
  | _ -> false


ghost
fn intro_context_and_repr_tag_related (c:context_t) (r:context_repr_t)
  requires context_perm c r
  ensures context_perm c r ** pure (context_and_repr_tag_related c r)
{
  let b = context_and_repr_tag_related c r;
  if b {
    ()
  } else {
    rewrite (context_perm c r) as (pure False);
    unreachable ()
  }
}



ghost
fn rewrite_context_perm_engine (ec:engine_context_t) (#r:context_repr_t)
  requires context_perm (Engine_context ec) r
  returns uds:Ghost.erased (Seq.seq U8.t)
  ensures engine_context_perm ec uds ** pure (r == Engine_context_repr uds)
{
  match r {
    Engine_context_repr uds -> {
      unfold context_perm;
      hide uds
    }
    L0_context_repr _ -> {
      rewrite (context_perm (Engine_context ec) r) as
              (pure False);
      unreachable ()

    }
    L1_context_repr _ -> {
      rewrite (context_perm (Engine_context ec) r) as
              (pure False);
      unreachable ()

    }

  }
}



ghost
fn rewrite_context_perm_l0 (lc:l0_context_t) (#r:context_repr_t)
  requires context_perm (L0_context lc) r
  returns lrepr:Ghost.erased l0_context_repr_t
  ensures l0_context_perm lc lrepr ** pure (r == L0_context_repr lrepr)
{
  match r {
    L0_context_repr lrepr -> {
      unfold context_perm;
      hide lrepr
    }
    Engine_context_repr _ -> {
      rewrite (context_perm (L0_context lc) r) as
              (pure False);
      unreachable ()
    }
    L1_context_repr _ -> {
      rewrite (context_perm (L0_context lc) r) as
              (pure False);
      unreachable ()
    }
  }
}



ghost
fn rewrite_context_perm_l1 (lc:l1_context_t) (#r:context_repr_t)
  requires context_perm (L1_context lc) r
  returns lrepr:Ghost.erased l1_context_repr_t
  ensures l1_context_perm lc lrepr ** pure (r == L1_context_repr lrepr)
{
  match r {
    L1_context_repr lrepr -> {
      unfold context_perm;
      hide lrepr
    }
    Engine_context_repr _ -> {
      rewrite (context_perm (L1_context lc) r) as
              (pure False);
      unreachable ()
    }
    L0_context_repr _ -> {
      rewrite (context_perm (L1_context lc) r) as
              (pure False);
      unreachable ()
    }
  }
}


noeq
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t

noeq
type repr_t =
  | Engine_repr : r:engine_record_repr -> repr_t
  | L0_repr     : r:l0_record_repr_t -> repr_t

let record_perm ([@@@mkey] record:record_t) (p:perm) (repr:repr_t)  : slprop = 
  match record, repr with
  | Engine_record r, Engine_repr r0 -> engine_record_perm r p r0
  | L0_record r, L0_repr r0 -> l0_record_perm r p r0
  | _ -> pure False

let record_perm_and_repr_tag_related (r:record_t) (repr:repr_t) : bool =
  match r, repr with
  | Engine_record _, Engine_repr _
  | L0_record _, L0_repr _ -> true
  | _ -> false


ghost
fn intro_record_and_repr_tag_related (r:record_t) (p:perm) (repr:repr_t)
  requires record_perm r p repr
  ensures record_perm r p repr **
          pure (record_perm_and_repr_tag_related r repr)
{
  let b = record_perm_and_repr_tag_related r repr;
  if b {
    ()
  } else {
    rewrite (record_perm r p repr) as (pure False);
    unreachable ()
  }
}



ghost
fn rewrite_record_perm_engine (er:engine_record_t) (#p:perm) (#repr:repr_t)
  requires record_perm (Engine_record er) p repr
  returns erepr:Ghost.erased engine_record_repr
  ensures engine_record_perm er p erepr ** pure (repr == Engine_repr erepr)
{
  match repr {
    Engine_repr erepr -> {
      unfold record_perm;
      hide erepr
    }
    L0_repr _ -> {
      rewrite record_perm (Engine_record er) p repr
           as pure False;
      unreachable ()
    }
  }
}



ghost
fn rewrite_record_perm_l0 (lr:l0_record_t) (#p:perm) (#repr:repr_t)
  requires record_perm (L0_record lr) p repr
  returns r0:Ghost.erased l0_record_repr_t
  ensures l0_record_perm lr p r0 ** pure (repr == L0_repr r0)
{
  match repr {
    Engine_repr _ -> {
      rewrite record_perm (L0_record lr) p repr
           as pure False;
      unreachable ()
    }
    L0_repr r0 -> {
      unfold record_perm;
      hide r0
    }
  }
}

