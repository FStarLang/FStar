module L0Crypto
open Pulse.Lib.Pervasives
open Pulse.Class.BoundedIntegers
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
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
  : elseq U8.t v32us & elseq U8.t v32us

```pulse
fn derive_key_pair
  (pub : A.larray U8.t (US.v v32us))
  (priv: A.larray U8.t (US.v v32us))
  (ikm_len: hkdf_ikm_len) 
  (ikm: A.array U8.t)
  (lbl_len: hkdf_lbl_len) 
  (lbl: A.array U8.t)
  (#ikm_perm #lbl_perm:perm)
  (#_pub_seq #_priv_seq:erased (elseq U8.t v32us))
  (#ikm_seq #lbl_seq:erased (Seq.seq U8.t))
  requires (
    A.pts_to pub full_perm _pub_seq ** 
    A.pts_to priv full_perm _priv_seq ** 
    A.pts_to ikm ikm_perm ikm_seq ** 
    A.pts_to lbl lbl_perm lbl_seq
  )
  ensures (
    A.pts_to ikm ikm_perm ikm_seq ** 
    A.pts_to lbl lbl_perm lbl_seq **
    exists (pub_seq priv_seq:Seq.seq U8.t). (
      A.pts_to pub full_perm pub_seq ** 
      A.pts_to priv full_perm priv_seq **
      pure ((pub_seq, priv_seq) == derive_key_pair_spec ikm_len ikm_seq lbl_len lbl_seq)
    ))
{
  admit()
}
```

let derive_DeviceID_spec
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi: Seq.seq U8.t) (* should be length 32 *)
  (l0_label_DeviceID_len: hkdf_lbl_len)
  (l0_label_DeviceID: Seq.seq U8.t)
: elseq U8.t v32us & elseq U8.t v32us
= let cdigest = spec_hash alg cdi in
  derive_key_pair_spec
    (* ikm *) dig_len cdigest
    (* lbl *) l0_label_DeviceID_len l0_label_DeviceID

```pulse 
fn derive_DeviceID
  (alg:alg_t)
  (deviceID_pub:A.larray U8.t (US.v v32us))
  (deviceID_priv:A.larray U8.t (US.v v32us))
  (cdi:A.larray U8.t (US.v dice_digest_len))
  (deviceID_label_len:hkdf_lbl_len)
  (deviceID_label:A.larray U8.t (US.v deviceID_label_len))
  (#cdi0 #deviceID_label0:erased (Seq.seq U8.t))
  (#deviceID_pub0 #deviceID_priv0:erased (elseq U8.t v32us))
  requires (
    A.pts_to cdi full_perm cdi0 **
    A.pts_to deviceID_label full_perm deviceID_label0 **
    A.pts_to deviceID_pub full_perm deviceID_pub0 **
    A.pts_to deviceID_priv full_perm deviceID_priv0 **
    pure (valid_hkdf_ikm_len (digest_len alg))
  )
  ensures (
    A.pts_to cdi full_perm cdi0 **
    A.pts_to deviceID_label full_perm deviceID_label0 **
    (exists (deviceID_pub1 deviceID_priv1:elseq U8.t v32us). (
        A.pts_to deviceID_pub full_perm deviceID_pub1 **
        A.pts_to deviceID_priv full_perm deviceID_priv1 **
        pure (
          valid_hkdf_ikm_len (digest_len alg) /\
          derive_DeviceID_spec alg (digest_len alg) cdi0 deviceID_label_len deviceID_label0 
            == (deviceID_pub1, deviceID_priv1)
        )
      ))
  )
{
  let cdigest = A.alloc 0uy (digest_len alg);
  hacl_hash alg dice_digest_len cdi cdigest;

  derive_key_pair
    deviceID_pub deviceID_priv
    (digest_len alg) cdigest
    deviceID_label_len deviceID_label;

  A.free cdigest;
}
```

let derive_AliasKey_spec
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi: Seq.seq U8.t)  (* should be length 32 *)
  (fwid: Seq.seq U8.t) (* should be length 32 *)
  (l0_label_AliasKey_len: hkdf_lbl_len)
  (l0_label_AliasKey: Seq.seq U8.t)
: elseq U8.t v32us & elseq U8.t v32us
= let cdigest = spec_hash alg cdi in
  let adigest = spec_hmac alg cdigest fwid in
  derive_key_pair_spec
    (* ikm *) dig_len adigest
    (* lbl *) l0_label_AliasKey_len l0_label_AliasKey

```pulse 
fn derive_AliasKey
  (alg:alg_t)
  (aliasKey_pub: A.larray U8.t (US.v v32us))
  (aliasKey_priv: A.larray U8.t (US.v v32us))
  (cdi: A.larray U8.t (US.v dice_digest_len))
  (fwid: A.larray U8.t (US.v v32us))
  (aliasKey_label_len: hkdf_lbl_len)
  (aliasKey_label: A.larray U8.t (US.v aliasKey_label_len))
  (#cdi0 #fwid0 #aliasKey_label0:erased (Seq.seq U8.t))
  (#aliasKey_pub0 #aliasKey_priv0:erased (elseq U8.t v32us))
  requires (
    A.pts_to cdi full_perm cdi0 **
    A.pts_to fwid full_perm fwid0 **
    A.pts_to aliasKey_label full_perm aliasKey_label0 **
    A.pts_to aliasKey_pub full_perm aliasKey_pub0 **
    A.pts_to aliasKey_priv full_perm aliasKey_priv0 **
    pure (is_hashable_len (digest_len alg) /\ valid_hkdf_ikm_len (digest_len alg))
  )
  ensures (
    A.pts_to cdi full_perm cdi0 **
    A.pts_to fwid full_perm fwid0 **
    A.pts_to aliasKey_label full_perm aliasKey_label0 **
    (exists (aliasKey_pub1 aliasKey_priv1:elseq U8.t v32us). (
        A.pts_to aliasKey_pub full_perm aliasKey_pub1 **
        A.pts_to aliasKey_priv full_perm aliasKey_priv1 **
        pure (
          is_hashable_len (digest_len alg) /\ 
          valid_hkdf_ikm_len (digest_len alg) /\
          derive_AliasKey_spec alg (digest_len alg) cdi0 fwid0 aliasKey_label_len aliasKey_label0 
            == (aliasKey_pub1, aliasKey_priv1)
        )
      ))
  )
{
  let cdigest = A.alloc 0uy (digest_len alg);
  let adigest = A.alloc 0uy (digest_len alg);

  hacl_hash alg dice_digest_len cdi cdigest;
  is_hashable_len_32;
  hacl_hmac alg adigest cdigest (digest_len alg) fwid v32us;

  derive_key_pair
    aliasKey_pub aliasKey_priv
    (digest_len alg) adigest
    aliasKey_label_len aliasKey_label;

  A.free cdigest;
  A.free adigest;
}
```

let derive_AuthKeyID_spec
  (alg:alg_t)
  (deviceID_pub: Seq.seq U8.t) (* should be length 32 *)
: Seq.seq U8.t (* should be length 20 *)
= spec_hash alg deviceID_pub

```pulse 
fn derive_AuthKeyID
  (alg:alg_t)
  (authKeyID: A.larray U8.t (US.v (digest_len alg)))
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (#authKeyID0:erased (Seq.seq U8.t))
  (#deviceID_pub0:erased (elseq U8.t v32us))
  requires (
    A.pts_to deviceID_pub full_perm deviceID_pub0 **
    A.pts_to authKeyID full_perm authKeyID0 
  )
  ensures (
    A.pts_to deviceID_pub full_perm deviceID_pub0 **
    exists (authKeyID1:Seq.seq U8.t). (
      A.pts_to authKeyID full_perm authKeyID1 **
      pure (Seq.equal (derive_AuthKeyID_spec alg deviceID_pub0) authKeyID1)
    )
  )
{
  is_hashable_len_32;
  hacl_hash alg v32us deviceID_pub authKeyID #full_perm #(coerce v32us deviceID_pub0);
}
```