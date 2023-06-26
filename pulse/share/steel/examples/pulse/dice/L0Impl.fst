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
fn get_witness (x:A.array U8.t) (#y:Ghost.erased (Seq.seq U8.t))
requires A.pts_to x full_perm y
returns z:Ghost.erased (Seq.seq U8.t)
ensures A.pts_to x full_perm y ** pure (y==z)
{   
    y
}
```


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

  let s1 = get_witness (l0.deviceID_pub);
  let s2 = get_witness (l0.deviceID_priv);
  let s3 = get_witness (l0.aliasKey_pub);
  let s4 = get_witness (l0.aliasKey_priv);
  let s5 = get_witness (l0.authKeyID);

  fold (l0_perm l0 (l0_step1_repr_post_state vl0 s1 s2 s3 s4 s5));
  ()
}
```

(* ------- L0 CORE STEP 2 ------- *)

let l0_step2_repr_post_state (vl0:l0_repr) (l:U32.t) (s:elseq U8.t (U32.v l))
  = { vl0 with 
      deviceIDCRI_len = l;
      deviceIDCRI_buf = s;
    }

assume 
val spec_sign_and_finalize_deviceIDCSR
  (deviceID_priv: Seq.seq U8.t)
  (deviceIDCRI_len: U32.t)
  (deviceIDCRI_seq: Seq.seq U8.t)
  // : deviceIDCSR_t deviceIDCRI_len
  : Seq.seq U8.t

assume
val create_deviceIDCRI_spec
  (version: U32.t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  (ku: U32.t)
  (deviceID_pub: Seq.seq U8.t)
  : deviceIDCRI_t

```pulse
fn create_deviceIDCRI
  (l0: l0_record)
  (deviceIDCSR: deviceIDCSR_ingredients_t)
  (aliasKeyCRT: aliasKeyCRT_ingredients_t)
  (#vl0: Ghost.erased l0_repr)
  requires l0_perm l0 vl0
  ensures (
    exists (vl0_:l0_repr). 
      l0_perm l0 vl0_ **
      pure (
        vl0_.deviceIDCRI_len == len_of_deviceIDCRI
                                  deviceIDCSR.version
                                  deviceIDCSR.s_common
                                  deviceIDCSR.s_org
                                  deviceIDCSR.s_country /\
        Seq.equal 
          vl0_.deviceIDCRI_buf
          (spec_serialize_deviceIDCRI (spec_x509_get_deviceIDCRI
                                        deviceIDCSR.version
                                        deviceIDCSR.s_common
                                        deviceIDCSR.s_org
                                        deviceIDCSR.s_country
                                        deviceIDCSR.ku
                                        vl0.deviceID_pub))
        )
  )
{
  unfold (l0_perm l0 vl0);

  let deviceIDCRI_len = len_of_deviceIDCRI
                          deviceIDCSR.version
                          deviceIDCSR.s_common
                          deviceIDCSR.s_org
                          deviceIDCSR.s_country;
  
  (write l0.deviceIDCRI_len, deviceIDCRI_len);

  let deviceIDCRI_buf = new_array 0uy (u32_to_us deviceIDCRI_len);

  let deviceIDCRI = x509_get_deviceIDCRI
                      deviceIDCSR.version
                      deviceIDCSR.s_common
                      deviceIDCSR.s_org
                      deviceIDCSR.s_country
                      deviceIDCSR.ku
                      l0.deviceID_pub;

  serialize_deviceIDCRI deviceIDCRI deviceIDCRI_len l0.deviceIDCRI_buf;
  let s = get_witness l0.deviceIDCRI_buf;

  // fold (l0_perm l0 (l0_step2_repr_post_state vl0 deviceIDCRI_len s));
  admit()

}
```

let l0_core_step2_pre
  (l0: l0_record)
  (deviceIDCSR: deviceIDCSR_ingredients_t)
  (aliasKeyCRT: aliasKeyCRT_ingredients_t)
  (vl0: Ghost.erased l0_repr)
  : prop = 
  U32.(0ul <^ vl0.deviceIDCRI_len) /\ 
  valid_deviceIDCSR_ingredients vl0.deviceIDCRI_len /\
  l0.deviceIDCSR_len == length_of_deviceIDCSR vl0.deviceIDCRI_len


let l0_core_step2_post
  (l0: l0_record)
  (deviceIDCSR: deviceIDCSR_ingredients_t)
  (aliasKeyCRT: aliasKeyCRT_ingredients_t)
  (vl0: Ghost.erased l0_repr)
  : prop = 
  vl0.deviceIDCRI_len == len_of_deviceIDCRI
                          deviceIDCSR.version
                          deviceIDCSR.s_common
                          deviceIDCSR.s_org
                          deviceIDCSR.s_country /\
  Seq.equal 
    vl0.deviceIDCRI_buf
    (spec_sign_and_finalize_deviceIDCSR
      vl0.deviceID_priv
      vl0.deviceIDCRI_len
      (spec_serialize_deviceIDCRI 
        (spec_x509_get_deviceIDCRI
            deviceIDCSR.version
            deviceIDCSR.s_common
            deviceIDCSR.s_org
            deviceIDCSR.s_country
            deviceIDCSR.ku
            vl0.deviceID_pub)))

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
  create_deviceIDCRI l0 deviceIDCSR aliasKeyCRT;
  admit()
(*
  create_deviceIDCRI
    (* version   *) csr_version
                    s_common
                    s_org
                    s_country
                    ku
    (* DeviceID  *) deviceID_pub
    (*DeviceIDCRI*) deviceIDCRI_len
                    deviceIDCRI_buf;
  (**) let hs2 = HST.get () in

  (**) assert (
    let deviceIDCRI: deviceIDCRI_t = create_deviceIDCRI_spec
                                                                      (csr_version)
                                                                      (s_common)
                                                                      (s_org)
                                                                      (s_country)
                                                                      (ku)
                                                                      (B.as_seq h0 deviceID_pub) in
    (* Prf *) lemma_serialize_deviceIDCRI_size_exact deviceIDCRI;
    B.as_seq hs2 deviceIDCRI_buf == serialize_deviceIDCRI `serialize` deviceIDCRI
  );

  (**) B.modifies_trans B.loc_none h0 hs1 (B.loc_buffer deviceIDCRI_buf) hs2;
  (**) B.modifies_buffer_elim deviceID_priv (B.loc_buffer deviceIDCRI_buf) h0 hs2;
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