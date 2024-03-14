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

module L0Core
open Pulse.Lib.Pervasives
open Pulse.Lib.BoundedIntegers
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open L0Types
open L0Crypto
open X509
open HACL

```pulse
fn create_deviceIDCRI
  (#pub_perm:perm)
  (#pub_seq #_buf:erased (Seq.seq U8.t))
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (deviceIDCRI_len: US.t)
  (deviceIDCRI_buf: A.larray U8.t (US.v deviceIDCRI_len))
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  requires 
    A.pts_to deviceID_pub #pub_perm pub_seq **
    A.pts_to deviceIDCRI_buf _buf **
    pure (
      deviceIDCRI_len == snd (len_of_deviceIDCRI deviceIDCSR_ingredients)
    )
  returns deviceIDCSR_ingredients_res:deviceIDCSR_ingredients_t
  ensures
    exists* (buf:Seq.seq U8.t).
      A.pts_to deviceID_pub #pub_perm pub_seq **
      A.pts_to deviceIDCRI_buf buf **
      pure (
        deviceIDCSR_ingredients_res == deviceIDCSR_ingredients /\
        buf `Seq.equal`
          (spec_serialize_deviceIDCRI 
            (spec_x509_get_deviceIDCRI
              deviceIDCSR_ingredients.version
              deviceIDCSR_ingredients.s_common
              deviceIDCSR_ingredients.s_org
              deviceIDCSR_ingredients.s_country
              deviceIDCSR_ingredients.ku
              pub_seq) 
            deviceIDCRI_len)
      )
{
  let deviceIDCRI = x509_get_deviceIDCRI deviceIDCSR_ingredients deviceID_pub;
  serialize_deviceIDCRI (snd deviceIDCRI) deviceIDCRI_len deviceIDCRI_buf;
  fst deviceIDCRI
}
```

// TODO: don't need full perm on all of these
```pulse
fn sign_and_finalize_deviceIDCSR
  (#priv_perm:perm)
  (#priv_seq #_cri_buf #_csr_buf:erased (Seq.seq U8.t))
  (deviceID_priv: A.larray U8.t (US.v v32us))
  (deviceIDCRI_len: US.t)
  (deviceIDCRI_buf: A.larray U8.t (US.v deviceIDCRI_len))
  (deviceIDCSR_len: US.t)
  (deviceIDCSR_buf: A.larray U8.t (US.v deviceIDCSR_len))
  (deviceIDCSR_ingredients: erased deviceIDCSR_ingredients_t)
  requires (
    A.pts_to deviceID_priv #priv_perm priv_seq **
    A.pts_to deviceIDCRI_buf _cri_buf **
    A.pts_to deviceIDCSR_buf _csr_buf **
    pure (
      deviceIDCRI_len == snd (len_of_deviceIDCRI (reveal deviceIDCSR_ingredients)) /\
      0 < US.v deviceIDCRI_len /\ 
      valid_deviceIDCSR_ingredients deviceIDCRI_len /\
      deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len
    ))
  ensures (
    exists* (csr_buf:Seq.seq U8.t).
    A.pts_to deviceID_priv #priv_perm priv_seq **
    A.pts_to deviceIDCRI_buf _cri_buf **
    A.pts_to deviceIDCSR_buf csr_buf **
    pure (
      csr_buf `Seq.equal`
        (spec_serialize_deviceIDCSR 
          deviceIDCRI_len 
          deviceIDCSR_len
          (spec_x509_get_deviceIDCSR
            deviceIDCRI_len
            _cri_buf
            (spec_ed25519_sign
              priv_seq
              _cri_buf)))
    ))
{
  let deviceIDCRI_sig = V.alloc 0uy 64sz;
  V.to_array_pts_to deviceIDCRI_sig;
  ed25519_sign (V.vec_to_array deviceIDCRI_sig) deviceID_priv deviceIDCRI_len deviceIDCRI_buf;
  let deviceIDCSR = x509_get_deviceIDCSR
                      deviceIDCRI_len
                      deviceIDCRI_buf
                      (V.vec_to_array deviceIDCRI_sig);
  V.to_vec_pts_to deviceIDCRI_sig;
  V.free deviceIDCRI_sig;
  serialize_deviceIDCSR deviceIDCRI_len deviceIDCSR deviceIDCSR_len deviceIDCSR_buf;
}
```

```pulse
fn create_aliasKeyTBS
  (#fwid_perm #authKey_perm #device_perm #aliasKey_perm:perm)
  (#fwid0 #authKeyID0 #deviceID_pub0 #aliasKey_pub0 #_buf:erased (Seq.seq U8.t))
  (fwid: A.larray U8.t (US.v v32us))
  (authKeyID: A.array U8.t)
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (aliasKey_pub: A.larray U8.t (US.v v32us))
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: A.larray U8.t (US.v aliasKeyTBS_len))
  (aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t)
  requires 
    A.pts_to fwid #fwid_perm fwid0 **
    A.pts_to authKeyID #authKey_perm authKeyID0 **
    A.pts_to deviceID_pub #device_perm deviceID_pub0 **
    A.pts_to aliasKey_pub #aliasKey_perm aliasKey_pub0 **
    A.pts_to aliasKeyTBS_buf _buf ** 
    pure (
      aliasKeyTBS_len == snd (len_of_aliasKeyTBS aliasKeyCRT_ingredients)
    )
  returns aliasKeyCRT_ingredients_res:aliasKeyCRT_ingredients_t
  ensures exists* (buf:Seq.seq U8.t).
    A.pts_to fwid #fwid_perm fwid0 **
    A.pts_to authKeyID #authKey_perm authKeyID0 **
    A.pts_to deviceID_pub #device_perm deviceID_pub0 **
    A.pts_to aliasKey_pub #aliasKey_perm aliasKey_pub0 **
    A.pts_to aliasKeyTBS_buf buf **
    pure (
      aliasKeyCRT_ingredients_res == aliasKeyCRT_ingredients /\
      buf `Seq.equal`
        (spec_serialize_aliasKeyTBS 
          (spec_x509_get_aliasKeyTBS
            aliasKeyCRT_ingredients
            fwid0
            deviceID_pub0
            aliasKey_pub0) 
          aliasKeyTBS_len)
    )
{
  let aliasKeyTBS = x509_get_aliasKeyTBS
                      aliasKeyCRT_ingredients
                      fwid
                      deviceID_pub
                      aliasKey_pub;

  serialize_aliasKeyTBS (snd aliasKeyTBS) aliasKeyTBS_len aliasKeyTBS_buf;
  fst aliasKeyTBS
}
```

```pulse
fn sign_and_finalize_aliasKeyCRT
  (#priv_perm:perm)
  (#priv_seq #_tbs_buf #_crt_buf:erased (Seq.seq U8.t))
  (deviceID_priv: A.larray U8.t (US.v v32us))
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: A.larray U8.t (US.v aliasKeyTBS_len))
  (aliasKeyCRT_len: US.t)
  (aliasKeyCRT_buf: A.larray U8.t (US.v aliasKeyCRT_len))
  (aliasKeyCRT_ingredients: erased aliasKeyCRT_ingredients_t)
  requires (
    A.pts_to deviceID_priv #priv_perm priv_seq **
    A.pts_to aliasKeyTBS_buf _tbs_buf **
    A.pts_to aliasKeyCRT_buf _crt_buf **
    pure (
      aliasKeyTBS_len == snd (len_of_aliasKeyTBS (reveal aliasKeyCRT_ingredients)) /\
      0 < US.v aliasKeyTBS_len /\ 
      valid_aliasKeyCRT_ingredients aliasKeyTBS_len /\
      aliasKeyCRT_len == length_of_aliasKeyCRT aliasKeyTBS_len
    ))
  ensures (
    exists* (crt_buf:Seq.seq U8.t). 
    A.pts_to deviceID_priv #priv_perm priv_seq **
    A.pts_to aliasKeyTBS_buf _tbs_buf **
    A.pts_to aliasKeyCRT_buf crt_buf **
    pure (
      crt_buf `Seq.equal`
        (spec_serialize_aliasKeyCRT 
          aliasKeyTBS_len 
          aliasKeyCRT_len
          (spec_x509_get_aliasKeyCRT
            aliasKeyTBS_len
            _tbs_buf
            (spec_ed25519_sign
              priv_seq
              _tbs_buf)))
    ))
{
  let aliasKeyTBS_sig = V.alloc 0uy 64sz;
  V.to_array_pts_to aliasKeyTBS_sig;

  ed25519_sign (V.vec_to_array aliasKeyTBS_sig) deviceID_priv aliasKeyTBS_len aliasKeyTBS_buf;

  let aliasKeyCRT = x509_get_aliasKeyCRT
                      aliasKeyTBS_len
                      aliasKeyTBS_buf
                      (V.vec_to_array aliasKeyTBS_sig);

  V.to_vec_pts_to aliasKeyTBS_sig;
  V.free aliasKeyTBS_sig;
                    
  serialize_aliasKeyCRT aliasKeyTBS_len aliasKeyCRT aliasKeyCRT_len aliasKeyCRT_buf;
}
```

(* pre / post conditions for l0 *)

noextract
let aliasKey_functional_correctness alg dig_len cdi fwid aliasKey_label_len aliasKey_label 
                  aliasKey_pub aliasKey_priv 
  = (aliasKey_pub, aliasKey_priv) == derive_AliasKey_spec alg dig_len cdi fwid aliasKey_label_len aliasKey_label

noextract
let deviceIDCSR_functional_correctness alg dig_len cdi deviceID_label_len deviceID_label 
                    deviceIDCSR_ingredients deviceIDCSR_len deviceIDCSR_buf
  = let (deviceID_pub, deviceID_priv) = (derive_DeviceID_spec alg dig_len cdi deviceID_label_len deviceID_label) in 
    let deviceIDCRI_len = snd (len_of_deviceIDCRI deviceIDCSR_ingredients) in
      let deviceIDCRI_buf = spec_serialize_deviceIDCRI 
                              (spec_x509_get_deviceIDCRI
                                deviceIDCSR_ingredients.version
                                deviceIDCSR_ingredients.s_common
                                deviceIDCSR_ingredients.s_org
                                deviceIDCSR_ingredients.s_country
                                deviceIDCSR_ingredients.ku
                                deviceID_pub) 
                              deviceIDCRI_len in 
    deviceIDCSR_buf `Seq.equal`
      (spec_serialize_deviceIDCSR 
        deviceIDCRI_len 
        deviceIDCSR_len
        (spec_x509_get_deviceIDCSR
          deviceIDCRI_len
          deviceIDCRI_buf
          (spec_ed25519_sign
            deviceID_priv
            deviceIDCRI_buf)))

noextract
let aliasKeyCRT_functional_correctness alg dig_len cdi fwid deviceID_label_len deviceID_label
                     aliasKeyCRT_ingredients aliasKeyCRT_len aliasKeyCRT_buf aliasKey_pub
  = let (deviceID_pub, deviceID_priv) = (derive_DeviceID_spec alg dig_len cdi deviceID_label_len deviceID_label) in 
    let authKeyID = derive_AuthKeyID_spec alg deviceID_pub in
    let aliasKeyTBS_len = snd (len_of_aliasKeyTBS aliasKeyCRT_ingredients) in
    let aliasKeyTBS_buf = (spec_serialize_aliasKeyTBS 
                            (spec_x509_get_aliasKeyTBS
                              aliasKeyCRT_ingredients
                              fwid
                              deviceID_pub
                              aliasKey_pub) 
                            aliasKeyTBS_len) in
    aliasKeyCRT_buf `Seq.equal` 
      (spec_serialize_aliasKeyCRT 
        aliasKeyTBS_len 
        aliasKeyCRT_len
        (spec_x509_get_aliasKeyCRT
          aliasKeyTBS_len
          aliasKeyTBS_buf
          (spec_ed25519_sign
            deviceID_priv
            aliasKeyTBS_buf)))

```pulse
ghost
fn l0_record_perm_aux (r1 r2:l0_record_t) (#p:perm) (#repr:l0_record_repr_t)
  requires l0_record_perm r1 p repr **
           pure (r1.fwid == r2.fwid /\
                  r1.deviceID_label_len == r2.deviceID_label_len /\
                  r1.deviceID_label == r2.deviceID_label /\
                  r1.aliasKey_label_len == r2.aliasKey_label_len /\
                  r1.aliasKey_label == r2.aliasKey_label)
  ensures l0_record_perm r2 p repr
{
  unfold (l0_record_perm r1 p repr);
  rewrite (V.pts_to r1.fwid #p repr.fwid) as (V.pts_to r2.fwid #p repr.fwid);
  rewrite (V.pts_to r1.deviceID_label #p repr.deviceID_label)
       as (V.pts_to r2.deviceID_label #p repr.deviceID_label);
  rewrite (V.pts_to r1.aliasKey_label #p repr.aliasKey_label)
       as (V.pts_to r2.aliasKey_label #p repr.aliasKey_label);
  fold (l0_record_perm r2 p repr)
}
```


```pulse
fn l0_main_aux
  (cdi: A.larray U8.t (US.v dice_digest_len))
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (deviceID_priv: A.larray U8.t (US.v v32us))
  (aliasKey_pub: A.larray U8.t (US.v v32us))
  (aliasKey_priv: A.larray U8.t (US.v v32us))
  (aliasKeyTBS_len:US.t)
  (aliasKeyCRT_len:US.t)
  (aliasKeyCRT: A.larray U8.t (US.v aliasKeyCRT_len))
  (deviceIDCRI_len:US.t)
  (deviceIDCSR_len:US.t)
  (deviceIDCSR: A.larray U8.t (US.v deviceIDCSR_len))
  ([@@@ Rust_mut_binder] record: l0_record_t)
  (#repr: erased l0_record_repr_t)
  (#cdi0 #deviceID_pub0 #deviceID_priv0 #aliasKey_pub0 #aliasKey_priv0 #aliasKeyCRT0 #deviceIDCSR0: erased (Seq.seq U8.t))
  (#cdi_perm #p:perm)
  requires (
    l0_record_perm record p repr **
    A.pts_to cdi #cdi_perm cdi0 **
    A.pts_to deviceID_pub deviceID_pub0 **
    A.pts_to deviceID_priv deviceID_priv0 **
    A.pts_to aliasKey_pub aliasKey_pub0 **
    A.pts_to aliasKey_priv aliasKey_priv0 **
    A.pts_to aliasKeyCRT aliasKeyCRT0 **
    A.pts_to deviceIDCSR deviceIDCSR0 **
    pure (
      deviceIDCSR_pre record.deviceIDCSR_ingredients deviceIDCRI_len deviceIDCSR_len /\
      aliasKeyCRT_pre record.aliasKeyCRT_ingredients aliasKeyTBS_len aliasKeyCRT_len
    ))
  returns record:l0_record_t
  ensures (
      l0_record_perm record p repr **
      A.pts_to cdi #cdi_perm cdi0 **
      (exists* (deviceID_pub1 deviceID_priv1 aliasKey_pub1 aliasKey_priv1
              aliasKeyCRT1 deviceIDCSR1:Seq.seq U8.t). (
        A.pts_to deviceID_pub deviceID_pub1 **
        A.pts_to deviceID_priv deviceID_priv1 **
        A.pts_to aliasKey_pub aliasKey_pub1 **
        A.pts_to aliasKey_priv aliasKey_priv1 **
        A.pts_to aliasKeyCRT aliasKeyCRT1 **
        A.pts_to deviceIDCSR deviceIDCSR1 **
        pure (
          valid_hkdf_ikm_len dice_digest_len /\
          aliasKey_functional_correctness
            dice_hash_alg dice_digest_len cdi0 repr.fwid
            record.aliasKey_label_len repr.aliasKey_label 
            aliasKey_pub1 aliasKey_priv1 /\
          deviceIDCSR_functional_correctness 
            dice_hash_alg dice_digest_len cdi0
            record.deviceID_label_len repr.deviceID_label record.deviceIDCSR_ingredients 
            deviceIDCSR_len deviceIDCSR1 /\       
          aliasKeyCRT_functional_correctness 
            dice_hash_alg dice_digest_len cdi0 repr.fwid
            record.deviceID_label_len repr.deviceID_label record.aliasKeyCRT_ingredients 
            aliasKeyCRT_len aliasKeyCRT1 aliasKey_pub1
      ))))
{
  unfold (l0_record_perm record p repr);

  V.to_array_pts_to record.deviceID_label;
  derive_DeviceID dice_hash_alg 
    deviceID_pub deviceID_priv cdi 
    record.deviceID_label_len (V.vec_to_array record.deviceID_label);
  V.to_vec_pts_to record.deviceID_label;

  V.to_array_pts_to record.fwid;
  V.to_array_pts_to record.aliasKey_label;
  derive_AliasKey dice_hash_alg
    aliasKey_pub aliasKey_priv cdi 
    (V.vec_to_array record.fwid) record.aliasKey_label_len (V.vec_to_array record.aliasKey_label);
  V.to_vec_pts_to record.fwid;
  V.to_vec_pts_to record.aliasKey_label;

  let authKeyID = V.alloc 0uy dice_digest_len;
  V.to_array_pts_to authKeyID;
  
  derive_AuthKeyID dice_hash_alg
    (V.vec_to_array authKeyID) deviceID_pub;

  let deviceIDCRI = V.alloc 0uy deviceIDCRI_len;
  V.to_array_pts_to deviceIDCRI;

  let deviceIDCSR_ingredients = create_deviceIDCRI deviceID_pub
    deviceIDCRI_len (V.vec_to_array deviceIDCRI)
    record.deviceIDCSR_ingredients;
  
  sign_and_finalize_deviceIDCSR deviceID_priv 
    deviceIDCRI_len (V.vec_to_array deviceIDCRI)
    deviceIDCSR_len deviceIDCSR
    deviceIDCSR_ingredients;

  let aliasKeyTBS = V.alloc 0uy aliasKeyTBS_len;
  V.to_array_pts_to aliasKeyTBS;

  V.to_array_pts_to record.fwid;
  let aliasKeyCRT_ingredients = create_aliasKeyTBS (V.vec_to_array record.fwid) (V.vec_to_array authKeyID)
    deviceID_pub aliasKey_pub
    aliasKeyTBS_len (V.vec_to_array aliasKeyTBS)
    record.aliasKeyCRT_ingredients;
  V.to_vec_pts_to record.fwid;

  sign_and_finalize_aliasKeyCRT deviceID_priv 
    aliasKeyTBS_len (V.vec_to_array aliasKeyTBS)
    aliasKeyCRT_len aliasKeyCRT
    record.aliasKeyCRT_ingredients;
  
  V.to_vec_pts_to authKeyID;
  V.free authKeyID;
  V.to_vec_pts_to deviceIDCRI;
  V.free deviceIDCRI;
  V.to_vec_pts_to aliasKeyTBS;
  V.free aliasKeyTBS;

  // // with s3. assert (A.pts_to deviceIDCRI s3);
  // // with s4. assert (A.pts_to aliasKeyTBS s4);

  fold l0_record_perm record p repr;

  let r1 = {
    fwid = record.fwid;
    deviceID_label_len = record.deviceID_label_len;
    deviceID_label = record.deviceID_label;
    aliasKey_label_len = record.aliasKey_label_len;
    aliasKey_label = record.aliasKey_label;
    deviceIDCSR_ingredients;
    aliasKeyCRT_ingredients;
  } <: l0_record_t;

  l0_record_perm_aux record r1;

  r1
}
```
let l0_main = l0_main_aux
