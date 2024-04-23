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

let engine_context_perm (c:engine_context_t) (uds_bytes:Seq.seq U8.t) : vprop
  = V.pts_to c.uds uds_bytes ** 
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
  repr:engine_record_repr;
}

let mk_l0_context_repr_t
  (uds:Seq.seq U8.t)
  (cdi:Seq.seq U8.t)
  (repr:engine_record_repr) 
: GTot l0_context_repr_t 
= {uds; cdi; repr}

let l0_context_perm (c:l0_context_t) (r:l0_context_repr_t): vprop
  = V.pts_to c.cdi r.cdi **
    pure (V.is_full_vec c.cdi
       /\ cdi_functional_correctness r.cdi r.uds r.repr
       /\ l0_is_authentic r.repr)

(* L1 Context *)
[@@ Rust_derive "Clone"]
noeq
type l1_context_t = { deviceID_priv: V.lvec U8.t (SZ.v v32us);
                      deviceID_pub: V.lvec U8.t (SZ.v v32us);   
                      aliasKey_priv: V.lvec U8.t (SZ.v v32us);
                      aliasKey_pub: V.lvec U8.t (SZ.v v32us);
                      aliasKeyCRT: V.vec U8.t;
                      deviceIDCSR: V.vec U8.t; }

let mk_l1_context_t deviceID_priv deviceID_pub aliasKey_priv aliasKey_pub aliasKeyCRT deviceIDCSR 
: l1_context_t
= {deviceID_priv; deviceID_pub; aliasKey_priv; aliasKey_pub; aliasKeyCRT; deviceIDCSR}

noeq
type l1_context_repr_t = {
  deviceID_label_len: hkdf_lbl_len;
  aliasKey_label_len: hkdf_lbl_len;
  deviceID_priv: Seq.seq U8.t;
  deviceID_pub: Seq.seq U8.t;
  aliasKey_priv: Seq.seq U8.t;
  aliasKey_pub: Seq.seq U8.t;
  aliasKeyCRT_len:SZ.t;
  aliasKeyCRT:Seq.seq U8.t;// aliasKeyCRT_len;
  deviceIDCSR_len:SZ.t;
  deviceIDCSR:Seq.seq U8.t;// deviceIDCSR_len;
  cdi:Seq.seq U8.t; // dice_digest_len;
  repr:l0_record_repr_t;
  deviceIDCSR_ingredients: deviceIDCSR_ingredients_t;
  aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t;
}

let mk_l1_context_repr_t 
  (deviceID_label_len:hkdf_lbl_len)
  (aliasKey_label_len:hkdf_lbl_len)
  (deviceID_priv:Seq.seq U8.t)
  (deviceID_pub:Seq.seq U8.t)
  (aliasKey_priv:Seq.seq U8.t)
  (aliasKey_pub:Seq.seq U8.t)
  (aliasKeyCRT_len:SZ.t)
  (aliasKeyCRT:Seq.seq U8.t)
  (deviceIDCSR_len:erased SZ.t)
  (deviceIDCSR:Seq.seq U8.t)
  (cdi:Seq.seq U8.t)
  (repr:l0_record_repr_t)
  (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
: GTot l1_context_repr_t 
= {deviceID_label_len; aliasKey_label_len; deviceID_priv; deviceID_pub; aliasKey_priv;
  aliasKey_pub; aliasKeyCRT_len; aliasKeyCRT; deviceIDCSR_len; deviceIDCSR;
  cdi; repr; deviceIDCSR_ingredients; aliasKeyCRT_ingredients}

let l1_context_perm (c:l1_context_t) (r:l1_context_repr_t)
  : vprop
  = V.pts_to c.deviceID_priv r.deviceID_priv **
    V.pts_to c.deviceID_pub r.deviceID_pub **
    V.pts_to c.aliasKey_priv r.aliasKey_priv **
    V.pts_to c.aliasKey_pub r.aliasKey_pub **
    V.pts_to c.aliasKeyCRT r.aliasKeyCRT **
    V.pts_to c.deviceIDCSR r.deviceIDCSR **
    pure (valid_hkdf_ikm_len dice_digest_len
       /\ aliasKey_functional_correctness
            dice_hash_alg dice_digest_len r.cdi r.repr.fwid
            r.aliasKey_label_len r.repr.aliasKey_label 
            r.aliasKey_pub r.aliasKey_priv
       /\ deviceIDCSR_functional_correctness 
            dice_hash_alg dice_digest_len r.cdi
            r.deviceID_label_len r.repr.deviceID_label r.deviceIDCSR_ingredients 
            r.deviceIDCSR_len r.deviceIDCSR       
       /\ aliasKeyCRT_functional_correctness 
            dice_hash_alg dice_digest_len r.cdi r.repr.fwid
            r.deviceID_label_len r.repr.deviceID_label r.aliasKeyCRT_ingredients 
            r.aliasKeyCRT_len r.aliasKeyCRT r.aliasKey_pub
       /\ V.is_full_vec c.deviceID_priv
       /\ V.is_full_vec c.deviceID_pub
       /\ V.is_full_vec c.aliasKey_priv
       /\ V.is_full_vec c.aliasKey_pub
       /\ V.is_full_vec c.aliasKeyCRT
       /\ V.is_full_vec c.deviceIDCSR)  

(* Generic Context *)
// unlike record_t (below), we require full permission on the resources inside
// the context because we will eventually free the resources when we destroy
// the context
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

let context_perm (context:context_t) (repr:context_repr_t): vprop = 
  match context, repr with
  | Engine_context c, Engine_context_repr uds -> engine_context_perm c uds
  | L0_context c, L0_context_repr r -> l0_context_perm c r
  | L1_context c, L1_context_repr r -> l1_context_perm c r
  | _ -> pure False

```pulse
ghost
fn rewrite_context_perm_engine (c:engine_context_t) (r:context_repr_t)
  requires context_perm (Engine_context c) r
  returns uds:Ghost.erased (Seq.seq U8.t)
  ensures engine_context_perm c uds ** pure (r == Engine_context_repr uds)
{
  match r {
    Engine_context_repr uds -> {
      rewrite (context_perm (Engine_context c) r) as
              (engine_context_perm c uds);
      hide uds
    }
    _ -> {
      assume_ (pure (~ (Engine_context_repr? r)));
      rewrite (context_perm (Engine_context c) r) as
              (pure False);
      unreachable ()

    }
  }
}
```

```pulse
ghost
fn rewrite_context_perm_l0 (c:l0_context_t) (r:context_repr_t)
  requires context_perm (L0_context c) r
  returns r1:Ghost.erased l0_context_repr_t
  ensures l0_context_perm c r1 ** pure (r == L0_context_repr r1)
{
  match r {
    L0_context_repr r1 -> {
      rewrite (context_perm (L0_context c) r) as
              (l0_context_perm c r1);
      hide r1
    }
    _ -> {
      assume_ (pure (~ (L0_context_repr? r)));
      rewrite (context_perm (L0_context c) r) as
              (pure False);
      unreachable ()
    }
  }
}
```

```pulse
ghost
fn rewrite_context_perm_l1 (c:l1_context_t) (r:context_repr_t)
  requires context_perm (L1_context c) r
  returns r1:Ghost.erased l1_context_repr_t
  ensures l1_context_perm c r1 ** pure (r == L1_context_repr r1)
{
  match r {
    L1_context_repr r1 -> {
      rewrite (context_perm (L1_context c) r) as
              (l1_context_perm c r1);
      hide r1
    }
    _ -> {
      assume_ (pure (~ (L1_context_repr? r)));
      rewrite (context_perm (L1_context c) r) as
              (pure False);
      unreachable ()
    }
  }
}
```

// In the implmentation, we store contexts as values in a global hash table
// so we need a way to store and retrieve permission on the context. We do this
// by keeping a tuple of the context along with a lock on the context permission
// let locked_context_t = c:context_t 
//                      & r:erased context_repr_t 
//                      & L.lock (context_perm c r)

(* Record *)
noeq
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t

noeq
type repr_t =
  | Engine_repr : r:engine_record_repr -> repr_t
  | L0_repr     : r:l0_record_repr_t -> repr_t

let record_perm (record:record_t) (p:perm) (repr:repr_t)  : vprop = 
  match record, repr with
  | Engine_record r, Engine_repr r0 -> engine_record_perm r p r0
  | L0_record r, L0_repr r0 -> l0_record_perm r p r0
  | _ -> pure False


```pulse
ghost
fn rewrite_record_perm_engine (r:engine_record_t) (p:perm) (repr:repr_t)
  requires record_perm (Engine_record r) p repr
  returns r0:Ghost.erased engine_record_repr
  ensures engine_record_perm r p r0 ** pure (repr == Engine_repr r0)
{
  match repr {
    Engine_repr r0 -> {
      rewrite (record_perm (Engine_record r) p repr)
          as  (engine_record_perm r p r0);
      hide r0
    }
    L0_repr _ -> {
      rewrite (record_perm (Engine_record r) p repr)
          as  (pure False);
      unreachable ()
    }
  }
}
```

```pulse
ghost
fn rewrite_record_perm_l0 (r:l0_record_t) (p:perm) (repr:repr_t)
  requires record_perm (L0_record r) p repr
  returns r0:Ghost.erased l0_record_repr_t
  ensures l0_record_perm r p r0 ** pure (repr == L0_repr r0)
{
  match repr {
    Engine_repr _ -> {
      rewrite (record_perm (L0_record r) p repr)
          as  (pure False);
      unreachable ()
    }
    L0_repr r0 -> {
      rewrite (record_perm (L0_record r) p repr)
          as  (l0_record_perm r p r0);
      hide r0
    }
  }
}
```
