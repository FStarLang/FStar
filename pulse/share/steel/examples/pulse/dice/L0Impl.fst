module L0Impl
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
open L0Crypto
open X509

```pulse
fn create_deviceIDCRI
  (deviceID_pub: A.array U8.t)
  (deviceIDCRI_len: R.ref U32.t)
  (deviceIDCRI_buf: A.array U8.t)
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  (#pub_perm:perm)
  (#_len:erased U32.t)
  (#pub#_buf:erased (Seq.seq U8.t))
  requires 
    A.pts_to deviceID_pub pub_perm pub **
    R.pts_to deviceIDCRI_len full_perm _len **
    A.pts_to deviceIDCRI_buf full_perm _buf
  ensures
    exists (len:U32.t) (buf:Seq.seq U8.t).
      A.pts_to deviceID_pub pub_perm pub **
      R.pts_to deviceIDCRI_len full_perm len **
      A.pts_to deviceIDCRI_buf full_perm buf **
      pure (
        len == len_of_deviceIDCRI deviceIDCSR_ingredients.version
                                  deviceIDCSR_ingredients.s_common
                                  deviceIDCSR_ingredients.s_org
                                  deviceIDCSR_ingredients.s_country /\
        buf `Seq.equal`
          (spec_serialize_deviceIDCRI (spec_x509_get_deviceIDCRI
                                        deviceIDCSR_ingredients.version
                                        deviceIDCSR_ingredients.s_common
                                        deviceIDCSR_ingredients.s_org
                                        deviceIDCSR_ingredients.s_country
                                        deviceIDCSR_ingredients.ku
                                        pub) len)
      )
{
  let len = len_of_deviceIDCRI
              deviceIDCSR_ingredients.version
              deviceIDCSR_ingredients.s_common
              deviceIDCSR_ingredients.s_org
              deviceIDCSR_ingredients.s_country;

  deviceIDCRI_len := len;
  
  let deviceIDCRI = x509_get_deviceIDCRI
                      deviceIDCSR_ingredients.version
                      deviceIDCSR_ingredients.s_common
                      deviceIDCSR_ingredients.s_org
                      deviceIDCSR_ingredients.s_country
                      deviceIDCSR_ingredients.ku
                      deviceID_pub;

  serialize_deviceIDCRI deviceIDCRI len deviceIDCRI_buf;

  ()
}
```

// TODO: don't need full perm on all of these
// TODO: we never set deviceIDCSR_len
```pulse
fn sign_and_finalize_deviceIDCSR
  (deviceID_priv: A.array U8.t)
  (deviceIDCRI_len: R.ref U32.t)
  (deviceIDCRI_buf: A.array U8.t)
  (deviceIDCSR_len: R.ref U32.t)
  (deviceIDCSR_buf: A.array U8.t)
  (#priv_perm:perm)
  (#_cri_len#_csr_len:erased U32.t)
  (#priv#_cri_buf#_csr_buf:erased (Seq.seq U8.t))
  requires (
    A.pts_to deviceID_priv priv_perm priv **
    R.pts_to deviceIDCRI_len full_perm _cri_len **
    A.pts_to deviceIDCRI_buf full_perm _cri_buf **
    R.pts_to deviceIDCSR_len full_perm _csr_len **
    A.pts_to deviceIDCSR_buf full_perm _csr_buf **
    pure (
      U32.(0ul <^ _cri_len) /\ 
      valid_deviceIDCSR_ingredients _cri_len /\
      _csr_len == length_of_deviceIDCSR _cri_len
    ))
  ensures (
    exists (csr_buf:Seq.seq U8.t). 
    A.pts_to deviceID_priv priv_perm priv **
    R.pts_to deviceIDCRI_len full_perm _cri_len **
    A.pts_to deviceIDCRI_buf full_perm _cri_buf **
    R.pts_to deviceIDCSR_len full_perm _csr_len **
    A.pts_to deviceIDCSR_buf full_perm csr_buf **
    pure (
      csr_buf `Seq.equal`
        (spec_serialize_deviceIDCSR _cri_len 
                                    _csr_len
                                    (spec_x509_get_deviceIDCSR
                                      _cri_len
                                      _cri_buf
                                      (spec_ed25519_sign
                                        priv
                                        _cri_buf)))
    ))
{
  let deviceIDCRI_len_v = !deviceIDCRI_len;
  let deviceIDCSR_len_v = !deviceIDCSR_len;
  let deviceIDCRI_sig = new_array 0uy (u32_to_us deviceIDCRI_len_v);

  ed25519_sign deviceIDCRI_sig deviceID_priv (u32_to_us deviceIDCRI_len_v) deviceIDCRI_buf;

  let deviceIDCSR = x509_get_deviceIDCSR
                      deviceIDCRI_len_v
                      deviceIDCRI_buf
                      deviceIDCRI_sig;
                    
  serialize_deviceIDCSR deviceIDCRI_len_v deviceIDCSR deviceIDCSR_buf deviceIDCSR_len_v;

  free_array deviceIDCRI_sig;

  ()
}
```

```pulse
fn create_aliasKeyTBS
  (fwid: A.larray U8.t 32)
  (authKeyID: A.array U8.t)
  (deviceID_pub: A.larray U8.t 32)
  (aliasKey_pub: A.larray U8.t 32)
  (aliasKeyTBS_len: R.ref U32.t)
  (aliasKeyTBS_buf: A.array U8.t)
  (aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t)
  (#fwid_perm #authKey_perm #device_perm #aliasKey_perm:perm)
  (#_len:erased U32.t)
  (#fwid0 #authKeyID0 #deviceID0 #aliasKey0 #_buf:erased (Seq.seq U8.t))
  requires 
    A.pts_to fwid fwid_perm fwid0 **
    A.pts_to authKeyID authKey_perm authKeyID0 **
    A.pts_to deviceID_pub device_perm deviceID0 **
    A.pts_to aliasKey_pub aliasKey_perm aliasKey0 **
    R.pts_to aliasKeyTBS_len full_perm _len **
    A.pts_to aliasKeyTBS_buf full_perm _buf
  ensures exists (len:U32.t) (buf:Seq.seq U8.t).
    A.pts_to fwid fwid_perm fwid0 **
    A.pts_to authKeyID authKey_perm authKeyID0 **
    A.pts_to deviceID_pub device_perm deviceID0 **
    A.pts_to aliasKey_pub aliasKey_perm aliasKey0 **
    R.pts_to aliasKeyTBS_len full_perm len **
    A.pts_to aliasKeyTBS_buf full_perm buf **
    pure (
      len == len_of_aliasKeyTBS
              aliasKeyCRT_ingredients.serialNumber
              aliasKeyCRT_ingredients.i_common
              aliasKeyCRT_ingredients.i_org
              aliasKeyCRT_ingredients.i_country
              aliasKeyCRT_ingredients.s_common
              aliasKeyCRT_ingredients.s_org
              aliasKeyCRT_ingredients.s_country
              aliasKeyCRT_ingredients.l0_version /\
      buf `Seq.equal`
        (spec_serialize_aliasKeyTBS (spec_x509_get_aliasKeyTBS
                                      aliasKeyCRT_ingredients
                                      fwid0
                                      deviceID0
                                      aliasKey0) 
                                    len)
    )
{
  let len = len_of_aliasKeyTBS
              aliasKeyCRT_ingredients.serialNumber
              aliasKeyCRT_ingredients.i_common
              aliasKeyCRT_ingredients.i_org
              aliasKeyCRT_ingredients.i_country
              aliasKeyCRT_ingredients.s_common
              aliasKeyCRT_ingredients.s_org
              aliasKeyCRT_ingredients.s_country
              aliasKeyCRT_ingredients.l0_version;

  aliasKeyTBS_len := len;

  let aliasKeyTBS = x509_get_aliasKeyTBS
                      aliasKeyCRT_ingredients
                      fwid
                      deviceID_pub
                      aliasKey_pub;

  serialize_aliasKeyTBS aliasKeyTBS len aliasKeyTBS_buf;
  ()
}
```

// TODO: don't need full perm on all of these
// TODO: we never set aliasKeyCRT_len
```pulse
fn sign_and_finalize_aliasKeyCRT
  (deviceID_priv: A.array U8.t)
  (aliasKeyTBS_len: R.ref U32.t)
  (aliasKeyTBS_buf: A.array U8.t)
  (aliasKeyCRT_len: R.ref U32.t)
  (aliasKeyCRT_buf: A.array U8.t)
  (#priv_perm:perm)
  (#_tbs_len#_crt_len:erased U32.t)
  (#priv#_tbs_buf#_crt_buf:erased (Seq.seq U8.t))
  requires (
    A.pts_to deviceID_priv priv_perm priv **
    R.pts_to aliasKeyTBS_len full_perm _tbs_len **
    A.pts_to aliasKeyTBS_buf full_perm _tbs_buf **
    R.pts_to aliasKeyCRT_len full_perm _crt_len **
    A.pts_to aliasKeyCRT_buf full_perm _crt_buf **
    pure (
      U32.(0ul <^ _tbs_len) /\ 
      valid_aliasKeyCRT_ingredients _tbs_len /\
      _crt_len == length_of_aliasKeyCRT _tbs_len
    ))
  ensures (
    exists (crt_buf:Seq.seq U8.t). 
    A.pts_to deviceID_priv priv_perm priv **
    R.pts_to aliasKeyTBS_len full_perm _tbs_len **
    A.pts_to aliasKeyTBS_buf full_perm _tbs_buf **
    R.pts_to aliasKeyCRT_len full_perm _crt_len **
    A.pts_to aliasKeyCRT_buf full_perm crt_buf **
    pure (
      crt_buf `Seq.equal`
        (spec_serialize_aliasKeyCRT _tbs_len 
                                    _crt_len
                                    (spec_x509_get_aliasKeyCRT
                                      _tbs_len
                                      _tbs_buf
                                      (spec_ed25519_sign
                                        priv
                                        _tbs_buf)))
    ))
{
  let aliasKeyTBS_len_v = !aliasKeyTBS_len;
  let aliasKeyCRT_len_v = !aliasKeyCRT_len;
  let aliasKeyTBS_sig = new_array 0uy (u32_to_us aliasKeyTBS_len_v);

  ed25519_sign aliasKeyTBS_sig deviceID_priv (u32_to_us aliasKeyTBS_len_v) aliasKeyTBS_buf;

  let aliasKeyCRT = x509_get_aliasKeyCRT
                      aliasKeyTBS_len_v
                      aliasKeyTBS_buf
                      aliasKeyTBS_sig;
                    
  serialize_aliasKeyCRT aliasKeyTBS_len_v aliasKeyCRT aliasKeyCRT_buf aliasKeyCRT_len_v;

  free_array aliasKeyTBS_sig;

  ()
}
```