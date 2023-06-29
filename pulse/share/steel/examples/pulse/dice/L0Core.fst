module L0Core

module R = Steel.ST.Reference
module A = Steel.ST.Array
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open HACL
open L0Types
open L0Impl
open L0Crypto
open X509

assume
val deviceIDCRI_pre (v:deviceIDCSR_ingredients_t) : prop

let deviceIDCSR_pre 
  (deviceIDCSR: deviceIDCSR_ingredients_t) 
  (deviceIDCSR_len: U32.t) 
  : prop
  = let deviceIDCRI_len = len_of_deviceIDCRI
                            deviceIDCSR.version
                            deviceIDCSR.s_common
                            deviceIDCSR.s_org
                            deviceIDCSR.s_country in
    U32.(0ul <^ deviceIDCRI_len) /\ 
    valid_deviceIDCSR_ingredients deviceIDCRI_len /\
    deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len

let aliasKeyCRT_pre 
  (aliasKeyCRT:aliasKeyCRT_ingredients_t) 
  (aliasKeyCRT_len:U32.t) 
  : prop
  = let aliasKeyTBS_len = len_of_aliasKeyTBS
                            aliasKeyCRT.serialNumber
                            aliasKeyCRT.i_common
                            aliasKeyCRT.i_org
                            aliasKeyCRT.i_country
                            aliasKeyCRT.s_common
                            aliasKeyCRT.s_org
                            aliasKeyCRT.s_country
                            aliasKeyCRT.l0_version in
    U32.(0ul <^ aliasKeyTBS_len) /\ 
    valid_aliasKeyCRT_ingredients aliasKeyTBS_len /\
    aliasKeyCRT_len == length_of_aliasKeyCRT aliasKeyTBS_len

let l0_pre
  (l0: l0_record)
  (vl0: l0_repr)
  : prop =
  deviceIDCRI_pre l0.deviceIDCSR_ingredients /\
  deviceIDCSR_pre l0.deviceIDCSR_ingredients vl0.deviceIDCSR_len /\
  aliasKeyCRT_pre l0.aliasKeyCRT_ingredients vl0.aliasKeyCRT_len /\
  valid_hkdf_lbl_len l0.deviceID_label_len /\
  valid_hkdf_lbl_len l0.aliasKey_label_len

assume
val aliasKey_post 
  (cdi: Seq.seq U8.t)
  (fwid: Seq.seq U8.t)
  (aliasKey_label_len: US.t)
  (aliasKey_label: Seq.seq U8.t)
  (aliasKey_pub: Seq.seq U8.t)
  (aliasKey_priv: Seq.seq U8.t)
  : vprop

assume
val deviceIDCSR_post
  (cdi: Seq.seq U8.t)
  (deviceID_label_len: US.t)
  (deviceID_label: Seq.seq U8.t)
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  (deviceIDCSR_len: U32.t)
  (deviceIDCSR_buf: Seq.seq U8.t)
  : vprop

assume
val aliasKeyCRT_post
  (cdi: Seq.seq U8.t)
  (fwid: Seq.seq U8.t)
  (deviceID_label_len: US.t)
  (deviceID_label: Seq.seq U8.t)
  (aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t)
  (aliasKeyCRT_len: U32.t)
  (aliasKeyCRT_buf: Seq.seq U8.t)
  (aliasKey_pub: Seq.seq U8.t)
  : vprop

let l0_post
  (l0: l0_record)
  (vl0: l0_repr)
  : vprop
  = aliasKey_post 
      vl0.cdi vl0.fwid l0.aliasKey_label_len vl0.aliasKey_label 
      vl0.aliasKey_pub vl0.aliasKey_priv `star`
    deviceIDCSR_post 
      vl0.cdi l0.deviceID_label_len vl0.deviceID_label l0.deviceIDCSR_ingredients 
      vl0.deviceIDCSR_len vl0.deviceIDCSR_buf `star`
    aliasKeyCRT_post 
      vl0.cdi vl0.fwid l0.deviceID_label_len vl0.deviceID_label l0.aliasKeyCRT_ingredients 
      vl0.aliasKeyCRT_len vl0.aliasKeyCRT_buf vl0.aliasKey_pub

```pulse
fn l0
  (l0: l0_record)
  (#_vl0: Ghost.erased l0_repr)
  requires (
    l0_perm l0 _vl0 **
    pure (l0_pre l0 _vl0)
  )
  ensures 
    exists (vl0: l0_repr). (
      l0_perm l0 vl0 **
      l0_post l0 vl0
    )
{
  unfold l0_perm l0 _vl0;

  dice_digest_len_is_hkdf_ikm;

  derive_DeviceID dice_hash_alg l0.deviceID_pub l0.deviceID_priv l0.cdi l0.deviceID_label_len l0.deviceID_label;
  derive_AliasKey dice_hash_alg l0.aliasKey_pub l0.aliasKey_priv l0.cdi l0.fwid l0.aliasKey_label_len l0.aliasKey_label;
  derive_AuthKeyID dice_hash_alg l0.authKeyID l0.deviceID_pub;

  create_deviceIDCRI l0.deviceID_pub l0.deviceIDCRI_len l0.deviceIDCRI_buf l0.deviceIDCSR_ingredients;

  sign_and_finalize_deviceIDCSR l0.deviceID_priv 
                                l0.deviceIDCRI_len l0.deviceIDCRI_buf 
                                l0.deviceIDCSR_len l0.deviceIDCSR_buf;

  create_aliasKeyTBS l0.fwid l0.authKeyID
                     l0.deviceID_pub l0.aliasKey_pub
                     l0.aliasKeyTBS_len l0.aliasKeyTBS_buf
                     l0.aliasKeyCRT_ingredients;

  sign_and_finalize_aliasKeyCRT l0.deviceID_priv 
                                l0.aliasKeyTBS_len l0.aliasKeyTBS_buf
                                l0.aliasKeyCRT_len l0.aliasKeyCRT_buf;

  // fold_l0_perm l0;
  admit()
}
```