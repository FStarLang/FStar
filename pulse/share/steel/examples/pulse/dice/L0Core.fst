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

assume
val aliasKeyCRT_pre 
  (v:aliasKeyCRT_ingredients_t) 
  (len:US.t) 
  : prop

let l0_pre
  (l0: l0_record)
  (vl0: l0_repr)
  : prop =
  deviceIDCRI_pre l0.deviceIDCSR_ingredients /\
  deviceIDCSR_pre l0.deviceIDCSR_ingredients vl0.deviceIDCSR_len /\
  aliasKeyCRT_pre l0.aliasKeyCRT_ingredients l0.aliasKeyCRT_len /\
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
  (aliasKeyCRT_len: US.t)
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
      l0.aliasKeyCRT_len vl0.aliasKeyCRT_buf vl0.aliasKey_pub

```pulse
fn l0
  (l0: l0_record)
  (#_vl0: Ghost.erased l0_repr)
  // (#pcdi #pfwid #pdeviceID_label #paliasKey_label: perm)
  requires (l0_perm l0 _vl0 `star`
            pure (l0_pre l0 _vl0))
  ensures exists (vl0: l0_repr). (
                    l0_perm l0 vl0 `star`
                    l0_post l0 vl0)
{
  unfold l0_perm l0 _vl0;

  dice_digest_len_is_hkdf_ikm;

  derive_DeviceID dice_hash_alg l0.deviceID_pub l0.deviceID_priv l0.cdi l0.deviceID_label_len l0.deviceID_label;
  derive_AliasKey dice_hash_alg l0.aliasKey_pub l0.aliasKey_priv l0.cdi l0.fwid l0.aliasKey_label_len l0.aliasKey_label;
  derive_authkeyID dice_hash_alg l0.authKeyID l0.deviceID_pub;

  create_deviceIDCRI l0.deviceID_pub l0.deviceIDCRI_len l0.deviceIDCRI_buf l0.deviceIDCSR_ingredients;

  let deviceIDCRI_len = !l0.deviceIDCRI_len;
  let deviceIDCSR_len = !l0.deviceIDCSR_len;
  
  sign_and_finalize_deviceIDCSR l0.deviceID_priv 
                                l0.deviceIDCRI_len l0.deviceIDCRI_buf 
                                l0.deviceIDCSR_len l0.deviceIDCSR_buf;

  fold_l0_perm l0;

  admit()

//   l0_core_step3
//     (aliasKeyCRT_ingredients.aliasKeyCrt_version)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_serialNumber)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_i_common)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_i_org)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_i_country)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_notBefore)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_notAfter)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_s_common)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_s_org)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_s_country)
//     (fwid)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_ku)
//     (authKeyID)
//     (aliasKeyCRT_ingredients.aliasKeyCrt_l0_version)
//     (* DeviceID  *) deviceID_pub
//                     deviceID_priv
//     (* AliasKey  *) aliasKey_pub
//     (*AliasKeyTBS*) aliasKeyCRT_len
//                     aliasKeyCRT_buf;
//   let _h_step3_post = HST.get () in

//   (**) B.modifies_trans (
//     B.loc_buffer deviceID_pub  `B.loc_union`
//     B.loc_buffer deviceID_priv `B.loc_union`
//     B.loc_buffer aliasKey_pub  `B.loc_union`
//     B.loc_buffer aliasKey_priv `B.loc_union`
//     B.loc_buffer authKeyID     `B.loc_union`
//     B.loc_buffer deviceIDCSR_buf
//   ) h0 _h_step3_pre (
//     B.loc_buffer aliasKeyCRT_buf
//   ) _h_step3_post;

//   (**) B.modifies_buffer_elim aliasKey_pub (
//          B.loc_buffer deviceIDCSR_buf `B.loc_union`
//          B.loc_buffer aliasKeyCRT_buf
//   ) _h_step1_post _h_step3_post;

// (* hsf *) let hsf = HST.get () in
//   HST.pop_frame ();
// (* hf *) let hf = HST.get () in
//   (**) B.popped_modifies hsf hf;
//   (**) B.modifies_buffer_elim deviceID_pub    (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
//   (**) B.modifies_buffer_elim aliasKey_pub    (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
//   (**) B.modifies_buffer_elim aliasKey_priv   (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
//   (**) B.modifies_buffer_elim deviceIDCSR_buf (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
//   (**) B.modifies_buffer_elim aliasKeyCRT_buf (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
//   lemma_l0_modifies
//     (byte_pub) (byte_sec)
//     (0x00uy) (u8 0x00)
//     (h0) (hf)
//     (deviceID_pub) (aliasKey_pub) (aliasKey_priv)
//     (deviceIDCSR_buf) (aliasKeyCRT_buf)
//     (hs0) (hs01) (hs02) (_h_step1_post) (_h_step2_post) (_h_step3_post) (hsf)
//     (deviceID_priv) (authKeyID);

//   assert (HST.equal_domains h0 hf)
}
```