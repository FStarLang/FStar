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


(* ------- L0 CORE STEP 1 ------- *)

let l0_step1_repr_post_state (vl0:l0_repr) (s1 s2 s3 s4 s5:_) 
  = { vl0 with 
      deviceID_pub = s1;
      deviceID_priv = s2;
      aliasKey_pub = s3;
      aliasKey_priv = s4;
      authKeyID = s5;
    }

let l0_core_step1_post
  (l0: l0_record)
  (vl0: l0_repr)
  (alg:alg_t)
  : prop = 
    valid_hkdf_ikm_len (digest_len alg) /\
    derive_DeviceID_spec alg (digest_len alg) vl0.cdi l0.deviceID_label_len vl0.deviceID_label
      == (vl0.deviceID_pub, vl0.deviceID_priv) /\
    derive_AliasKey_spec alg (digest_len alg) vl0.cdi vl0.fwid l0.aliasKey_label_len vl0.aliasKey_label
      == (vl0.aliasKey_pub, vl0.aliasKey_priv) /\
    derive_authKeyID_spec alg vl0.deviceID_pub
      == vl0.authKeyID 

```pulse
fn l0_core_step1
  (l0: l0_record)
  (#vl0: Ghost.erased l0_repr)
  requires (
    l0_perm l0 vl0 `star`
    pure(valid_hkdf_lbl_len l0.deviceID_label_len /\
         valid_hkdf_lbl_len l0.aliasKey_label_len)
  )
  ensures (
    exists (vl0_:l0_repr). 
      l0_perm l0 vl0_ **
      pure (l0_core_step1_post l0 vl0_ dice_hash_alg)
  )
{
  dice_digest_len_is_hkdf_ikm;

  unfold (l0_perm l0 vl0);

  derive_DeviceID dice_hash_alg l0.deviceID_pub l0.deviceID_priv l0.cdi l0.deviceID_label_len l0.deviceID_label;
  derive_AliasKey dice_hash_alg l0.aliasKey_pub l0.aliasKey_priv l0.cdi l0.fwid l0.aliasKey_label_len l0.aliasKey_label;
  derive_authkeyID dice_hash_alg l0.authKeyID l0.deviceID_pub;
  
  fold_l0_perm l0;
  ()
}
```

(* ------- L0 CORE STEP 2 ------- *)

let l0_step2_repr_post_state (vl0:l0_repr) (l:U32.t) (s:Seq.seq U8.t)
  = { vl0 with 
      deviceIDCRI_len = l;
      deviceIDCRI_buf = s;
    }

```pulse
fn create_deviceIDCRI
  (deviceID_pub: A.array U8.t)
  (deviceIDCRI_len: R.ref U32.t)
  (deviceIDCRI_buf: A.array U8.t)
  (deviceIDCSR: deviceIDCSR_ingredients_t)
  (#pub_perm:perm)
  (#pub: erased (Seq.seq U8.t))
  (#_len:erased U32.t)
  (#_buf:erased (Seq.seq U8.t))
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
        len == len_of_deviceIDCRI deviceIDCSR.version
                                  deviceIDCSR.s_common
                                  deviceIDCSR.s_org
                                  deviceIDCSR.s_country /\
        buf `Seq.equal`
          (spec_serialize_deviceIDCRI (spec_x509_get_deviceIDCRI
                                        deviceIDCSR.version
                                        deviceIDCSR.s_common
                                        deviceIDCSR.s_org
                                        deviceIDCSR.s_country
                                        deviceIDCSR.ku
                                        pub) len)
      )
{
  let len = len_of_deviceIDCRI
                          deviceIDCSR.version
                          deviceIDCSR.s_common
                          deviceIDCSR.s_org
                          deviceIDCSR.s_country;

  deviceIDCRI_len := len;
  
  let deviceIDCRI = x509_get_deviceIDCRI
                      deviceIDCSR.version
                      deviceIDCSR.s_common
                      deviceIDCSR.s_org
                      deviceIDCSR.s_country
                      deviceIDCSR.ku
                      deviceID_pub;

  serialize_deviceIDCRI deviceIDCRI len deviceIDCRI_buf;

  ()
}
```

```pulse
fn sign_and_finalize_deviceIDCSR
  (deviceID_priv: A.array U8.t)
  (deviceIDCRI_len: R.ref U32.t)
  (deviceIDCRI_buf: A.array U8.t)
  (deviceIDCSR_len: R.ref U32.t)
  (deviceIDCSR_buf: A.array U8.t)
  (#priv_perm:perm)
  (#_cri_len#_csr_len:U32.t)
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
                                    (spec_sign_and_finalize_deviceIDCSR
                                      priv
                                      _cri_len
                                      _cri_buf))
    ))
{
  let deviceIDCRI_len_v = !deviceIDCRI_len;
  let deviceIDCRI_sig = new_array 0uy (u32_to_us deviceIDCRI_len_v);
  ed25519_sign deviceIDCRI_sig deviceID_priv (u32_to_us deviceIDCRI_len_v) deviceIDCRI_buf;
  // let deviceIDCSR = x509_get_deviceIDCSR
  //                     deviceIDCRI_len
  //                     deviceIDCRI_buf
  //                     deviceIDCRI_sig;
                    
  // serialize_deviceIDCSR deviceIDCRI_len deviceIDCSR deviceIDCRI_buf deviceIDCSR_len;
  admit()
}
```

let l0_core_step2_pre
  (l0: l0_record)
  (deviceIDCSR: deviceIDCSR_ingredients_t)
  (aliasKeyCRT: aliasKeyCRT_ingredients_t)
  (vl0: Ghost.erased l0_repr)
  : prop = 
  let deviceIDCRI_len = len_of_deviceIDCRI
                          deviceIDCSR.version
                          deviceIDCSR.s_common
                          deviceIDCSR.s_org
                          deviceIDCSR.s_country in
  U32.(0ul <^ deviceIDCRI_len) /\ 
  valid_deviceIDCSR_ingredients deviceIDCRI_len /\
  vl0.deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len


let l0_core_step2_post
  (l0: l0_record)
  (deviceIDCSR: deviceIDCSR_ingredients_t)
  (aliasKeyCRT: aliasKeyCRT_ingredients_t)
  (vl0: Ghost.erased l0_repr)
  : prop = 
  vl0.deviceIDCSR_buf `Seq.equal`
    (spec_serialize_deviceIDCSR vl0.deviceIDCRI_len 
                                vl0.deviceIDCSR_len
                                (spec_sign_and_finalize_deviceIDCSR
                                  vl0.deviceID_priv
                                  vl0.deviceIDCRI_len
                                  vl0.deviceIDCRI_buf))

```pulse
fn l0_core_step2
  (l0: l0_record)
  (deviceIDCSR: deviceIDCSR_ingredients_t)
  (aliasKeyCRT: aliasKeyCRT_ingredients_t)
  (#vl0: Ghost.erased l0_repr)
  requires (
    l0_perm l0 vl0 **
    pure (l0_core_step2_pre l0 deviceIDCSR aliasKeyCRT vl0)
  )
  ensures (
    exists (vl0_:l0_repr). 
      l0_perm l0 vl0_ **
      pure (l0_core_step2_post l0 deviceIDCSR aliasKeyCRT vl0_)
  )
{
  unfold (l0_perm l0 vl0);

  create_deviceIDCRI l0.deviceID_pub l0.deviceIDCRI_len l0.deviceIDCRI_buf deviceIDCSR;

  fold_l0_perm l0;

  with vl0_. assert l0_perm l0 vl0_;

  unfold (l0_perm l0 vl0_);

  let deviceIDCRI_len = !l0.deviceIDCRI_len;
  let deviceIDCSR_len = !l0.deviceIDCSR_len;

  sign_and_finalize_deviceIDCSR l0.deviceID_priv 
                                l0.deviceIDCRI_len l0.deviceIDCRI_buf 
                                l0.deviceIDCSR_len l0.deviceIDCSR_buf;

  fold_l0_perm l0;

  admit()
(*
  printf "Signing and finalizing DeviceID Certificate Signing Request\n" done;
  sign_and_finalize_deviceIDCSR
    (*Signing Key*) deviceID_priv
    (*DeviceIDCRI*) deviceIDCRI_len
                    deviceIDCRI_buf
    (*DeviceIDCSR*) deviceIDCSR_len
                    deviceIDCSR_buf;
  (**) let hs3 = HST.get () in

  (**) assert (
    let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = sign_and_finalize_deviceIDCSR_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (deviceIDCRI_len)
                                                                      (B.as_seq hs2 deviceIDCRI_buf) in
    (* Prf *) lemma_serialize_deviceIDCSR_size_exact deviceIDCRI_len deviceIDCSR;
    B.as_seq hs3 deviceIDCSR_buf == serialize_deviceIDCSR deviceIDCRI_len `serialize` deviceIDCSR
  );

  (**) assert (
    let deviceIDCRI_len: asn1_TLV_int32_of_type SEQUENCE = len_of_deviceIDCRI
                                                            csr_version
                                                            s_common
                                                            s_org
                                                            s_country in
    let deviceIDCRI: deviceIDCRI_t = create_deviceIDCRI_spec
                                                                      (csr_version)
                                                                      (s_common)
                                                                      (s_org)
                                                                      (s_country)
                                                                      (ku)
                                                                      (B.as_seq h0 deviceID_pub) in
    let deviceIDCRI_seq = serialize_deviceIDCRI `serialize` deviceIDCRI in
    let (* Prf *) _ = lemma_serialize_deviceIDCRI_size_exact deviceIDCRI in
    let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = sign_and_finalize_deviceIDCSR_spec
                                                                      (B.as_seq h0 deviceID_priv)
                                                                      (deviceIDCRI_len)
                                                                      (deviceIDCRI_seq) in
    (* Prf *) lemma_serialize_deviceIDCSR_size_exact deviceIDCRI_len deviceIDCSR;
    B.as_seq hs3 deviceIDCSR_buf == serialize_deviceIDCSR deviceIDCRI_len `serialize` deviceIDCSR
  );

  (**) B.modifies_trans (B.loc_buffer deviceIDCRI_buf) h0 hs2 (B.loc_buffer deviceIDCSR_buf) hs3;
  (**) let hsf = HST.get () in
  HST.pop_frame ();
  (**) let hf = HST.get () in
  (**) B.popped_modifies hsf hf;
  (**) B.modifies_buffer_elim deviceIDCSR_buf (B.loc_region_only false (HS.get_tip hsf)) hsf hf;
  (**) B.modifies_fresh_frame_popped h0 hs0 (
    B.loc_buffer deviceIDCSR_buf
  ) hsf hf;
()

*)
}
```

