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
val deviceid_len_is_valid' (len:US.t)
  : valid_hkdf_lbl_len len

let deviceid_len_is_valid = deviceid_len_is_valid'

assume 
val aliaskey_len_is_valid' (len:US.t)
  : valid_hkdf_lbl_len len
let aliaskey_len_is_valid = aliaskey_len_is_valid'

assume
val derive_key_pair_spec'
  (ikm_len: hkdf_ikm_len)
  (ikm: Seq.seq U8.t)
  (lbl_len: hkdf_lbl_len)
  (lbl: Seq.seq U8.t)
  : elseq U8.t v32us & elseq U8.t v32us
let derive_key_pair_spec = derive_key_pair_spec'

```pulse
fn derive_key_pair'
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
    A.pts_to pub _pub_seq ** 
    A.pts_to priv _priv_seq ** 
    A.pts_to ikm #ikm_perm ikm_seq ** 
    A.pts_to lbl #lbl_perm lbl_seq
  )
  ensures (
    A.pts_to ikm #ikm_perm ikm_seq ** 
    A.pts_to lbl #lbl_perm lbl_seq **
    exists (pub_seq priv_seq:elseq U8.t v32us). (
      A.pts_to pub pub_seq ** 
      A.pts_to priv priv_seq **
      pure ((pub_seq, priv_seq) == derive_key_pair_spec ikm_len ikm_seq lbl_len lbl_seq)
    ))
{
  admit()
}
```
let derive_key_pair = derive_key_pair'

```pulse 
fn derive_DeviceID'
  (alg:alg_t)
  (deviceID_pub:A.larray U8.t (US.v v32us))
  (deviceID_priv:A.larray U8.t (US.v v32us))
  (cdi:A.larray U8.t (US.v dice_digest_len))
  (deviceID_label_len:hkdf_lbl_len)
  (deviceID_label:A.larray U8.t (US.v deviceID_label_len))
  (#cdi0 #deviceID_label0:erased (Seq.seq U8.t))
  (#deviceID_pub0 #deviceID_priv0:erased (elseq U8.t v32us))
  (#cdi_perm #p:perm)
  requires (
    A.pts_to cdi #cdi_perm cdi0 **
    A.pts_to deviceID_label #p deviceID_label0 **
    A.pts_to deviceID_pub deviceID_pub0 **
    A.pts_to deviceID_priv deviceID_priv0 **
    pure (valid_hkdf_ikm_len (digest_len alg))
  )
  ensures (
    A.pts_to cdi #cdi_perm cdi0 **
    A.pts_to deviceID_label #p deviceID_label0 **
    (exists (deviceID_pub1 deviceID_priv1:elseq U8.t v32us). (
        A.pts_to deviceID_pub deviceID_pub1 **
        A.pts_to deviceID_priv deviceID_priv1 **
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
let derive_DeviceID = derive_DeviceID'

```pulse 
fn derive_AliasKey'
  (alg:alg_t)
  (aliasKey_pub: A.larray U8.t (US.v v32us))
  (aliasKey_priv: A.larray U8.t (US.v v32us))
  (cdi: A.larray U8.t (US.v dice_digest_len))
  (fwid: A.larray U8.t (US.v v32us))
  (aliasKey_label_len: hkdf_lbl_len)
  (aliasKey_label: A.larray U8.t (US.v aliasKey_label_len))
  (#cdi0 #fwid0 #aliasKey_label0:erased (Seq.seq U8.t))
  (#aliasKey_pub0 #aliasKey_priv0:erased (elseq U8.t v32us))
  (#cdi_perm #p:perm)
  requires (
    A.pts_to cdi #cdi_perm cdi0 **
    A.pts_to fwid #p fwid0 **
    A.pts_to aliasKey_label #p aliasKey_label0 **
    A.pts_to aliasKey_pub aliasKey_pub0 **
    A.pts_to aliasKey_priv aliasKey_priv0 **
    pure (is_hashable_len (digest_len alg) /\ valid_hkdf_ikm_len (digest_len alg))
  )
  ensures (
    A.pts_to cdi #cdi_perm cdi0 **
    A.pts_to fwid #p fwid0 **
    A.pts_to aliasKey_label #p aliasKey_label0 **
    (exists (aliasKey_pub1 aliasKey_priv1:elseq U8.t v32us). (
        A.pts_to aliasKey_pub aliasKey_pub1 **
        A.pts_to aliasKey_priv aliasKey_priv1 **
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
let derive_AliasKey = derive_AliasKey'


```pulse 
fn derive_AuthKeyID'
  (alg:alg_t)
  (authKeyID: A.larray U8.t (US.v (digest_len alg)))
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (#authKeyID0:erased (Seq.seq U8.t))
  (#deviceID_pub0:erased (elseq U8.t v32us))
  (#p:perm)
  requires (
    A.pts_to deviceID_pub #p deviceID_pub0 **
    A.pts_to authKeyID authKeyID0 
  )
  ensures (
    A.pts_to deviceID_pub #p deviceID_pub0 **
    exists (authKeyID1:Seq.seq U8.t). (
      A.pts_to authKeyID authKeyID1 **
      pure (Seq.equal (derive_AuthKeyID_spec alg deviceID_pub0) authKeyID1)
    )
  )
{
  is_hashable_len_32;
  hacl_hash alg v32us deviceID_pub authKeyID #p #(coerce v32us deviceID_pub0);
}
```
let derive_AuthKeyID = derive_AuthKeyID'