module L0Crypto
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

assume 
val deviceid_len_is_valid (len:US.t)
  : valid_hkdf_lbl_len len

assume 
val aliaskey_len_is_valid (len:US.t)
  : valid_hkdf_lbl_len len

assume
val derive_key_pair_spec
  (ikm_len: hkdf_ikm_len)
  (ikm: Seq.seq U8.t)
  (lbl_len: hkdf_lbl_len)
  (lbl: Seq.seq U8.t)
  : Seq.seq U8.t & Seq.seq U8.t (* should be length 32 *)

let derive_DeviceID_spec
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi: Seq.seq U8.t) (* should be length 32 *)
  (l0_label_DeviceID_len: hkdf_lbl_len)
  (l0_label_DeviceID: Seq.seq U8.t)
: Seq.seq U8.t & Seq.seq U8.t (* should be length 32 *)
= let cdigest = spec_hash alg cdi in
  derive_key_pair_spec
    (* ikm *) dig_len cdigest
    (* lbl *) l0_label_DeviceID_len l0_label_DeviceID

```pulse 
fn derive_DeviceID
  (alg:alg_t)
  (deviceID_pub: A.larray U8.t 32)
  (deviceID_priv: A.larray U8.t 32)
  (cdi: A.larray U8.t 32)
  (deviceID_label_len: hkdf_lbl_len)
  (deviceID_label: A.larray U8.t (US.v deviceID_label_len))
  (#cdi0 #deviceID_label0 #deviceID_pub0 #deviceID_priv0: Ghost.erased (Seq.seq U8.t))
  requires (
    A.pts_to cdi full_perm cdi0 `star`
    A.pts_to deviceID_label full_perm deviceID_label0 `star`
    A.pts_to deviceID_pub full_perm deviceID_pub0 `star`
    A.pts_to deviceID_priv full_perm deviceID_priv0
  )
  ensures (
    A.pts_to cdi full_perm cdi0 `star`
    A.pts_to deviceID_label full_perm deviceID_label0 `star`
    // (exists (deviceID_pub1:Seq.seq U8.t). A.pts_to deviceID_pub full_perm deviceID_pub1) `star`
    (exists (deviceID_pub1:Seq.seq U8.t) (deviceID_priv1:Seq.seq U8.t). (
        A.pts_to deviceID_pub full_perm deviceID_pub1 `star`
        A.pts_to deviceID_priv full_perm deviceID_priv1 `star`
        pure (valid_hkdf_ikm_len (digest_len alg) /\
              derive_DeviceID_spec alg (digest_len alg) cdi0 deviceID_label_len deviceID_label0 == (deviceID_pub1, deviceID_priv1))
      ))
  )
{
  admit()
}
```

let derive_AliasKey_spec
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi: Seq.seq U8.t)  (* should be length 32 *)
  (fwid: Seq.seq U8.t) (* should be length 32 *)
  (l0_label_AliasKey_len: hkdf_lbl_len)
  (l0_label_AliasKey: Seq.seq U8.t)
: Seq.seq U8.t & Seq.seq U8.t (* should be length 32 *)
= let cdigest = spec_hash alg cdi in
  let adigest = spec_hmac alg cdigest fwid in
  derive_key_pair_spec
    (* ikm *) dig_len adigest
    (* lbl *) l0_label_AliasKey_len l0_label_AliasKey

```pulse 
fn derive_AliasKey
  (alg:alg_t)
  (aliasKey_pub: A.larray U8.t 32)
  (aliasKey_priv: A.larray U8.t 32)
  (cdi: A.larray U8.t 32)
  (fwid: A.larray U8.t 32)
  (aliasKey_label_len: hkdf_lbl_len)
  (aliasKey_label: A.larray U8.t (US.v aliasKey_label_len))
  (#cdi0 #fwid0 #aliasKey_label0 #aliasKey_pub0 #aliasKey_priv0: Ghost.erased (Seq.seq U8.t))
  requires (
    A.pts_to cdi full_perm cdi0 `star`
    A.pts_to fwid full_perm fwid0 `star`
    A.pts_to aliasKey_label full_perm aliasKey_label0 `star`
    A.pts_to aliasKey_pub full_perm aliasKey_pub0 `star`
    A.pts_to aliasKey_priv full_perm aliasKey_priv0
  )
  ensures (
    A.pts_to cdi full_perm cdi0 `star`
    A.pts_to fwid full_perm fwid0 `star`
    A.pts_to aliasKey_label full_perm aliasKey_label0 `star`
    (exists (aliasKey_pub1:Seq.seq U8.t) (aliasKey_priv1:Seq.seq U8.t). (
        A.pts_to aliasKey_pub full_perm aliasKey_pub1 `star`
        A.pts_to aliasKey_priv full_perm aliasKey_priv1 `star`
        pure (valid_hkdf_ikm_len (digest_len alg) /\
              derive_AliasKey_spec alg (digest_len alg) cdi0 fwid0 aliasKey_label_len aliasKey_label0 == (aliasKey_pub1, aliasKey_priv1))
      ))
  )
{
  admit()
}
```

let derive_authKeyID_spec
  (alg:alg_t)
  (deviceID_pub: Seq.seq U8.t) (* should be length 32 *)
: Seq.seq U8.t (* should be length 20 *)
= spec_hash alg deviceID_pub

```pulse 
fn derive_authkeyID
  (alg:alg_t)
  (authKeyID: A.larray U8.t 32)
  (deviceID_pub: A.larray U8.t 32)
  (#authKeyID0 #deviceID_pub0: Ghost.erased (Seq.seq U8.t))
  requires (
    A.pts_to deviceID_pub full_perm deviceID_pub0 `star`
    A.pts_to authKeyID full_perm authKeyID0 
  )
  ensures (
    A.pts_to deviceID_pub full_perm deviceID_pub0 `star`
    (exists (authKeyID1:Seq.seq U8.t). (
        A.pts_to authKeyID full_perm authKeyID1 `star`
        pure (Seq.equal (derive_authKeyID_spec alg deviceID_pub0) authKeyID1)
      ))
  )
{
  admit()
}
```