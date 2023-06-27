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

let l0_step2_repr_post_state (vl0:l0_repr) (l:U32.t) (s:elseq U8.t (U32.v l))
  = { vl0 with 
      deviceIDCRI_len = l;
      deviceIDCRI_buf = s;
    }

let l0_repr_modifies_IDCRI_buf_len (vl0:l0_repr) (vl1:l0_repr) = 
  vl1 == { vl0 with deviceIDCRI_buf = vl1.deviceIDCRI_buf;
                    deviceIDCRI_len = vl1.deviceIDCRI_len }

```pulse
fn create_deviceIDCRI
  (l0: l0_record)
  (deviceIDCSR: deviceIDCSR_ingredients_t)
  (#vl0: Ghost.erased l0_repr)
  requires l0_perm l0 vl0
  ensures (
    exists (vl0_:l0_repr). 
      l0_perm l0 vl0_ **
      pure (
        l0_repr_modifies_IDCRI_buf_len vl0 vl0_ /\
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
                                        vl0_.deviceID_pub)
                                      vl0_.deviceIDCRI_len)
        )
  )
{
  unfold (l0_perm l0 vl0);

  let deviceIDCRI_len = len_of_deviceIDCRI
                          deviceIDCSR.version
                          deviceIDCSR.s_common
                          deviceIDCSR.s_org
                          deviceIDCSR.s_country;
  
  l0.deviceIDCRI_len := deviceIDCRI_len;

  let deviceIDCRI = x509_get_deviceIDCRI
                      deviceIDCSR.version
                      deviceIDCSR.s_common
                      deviceIDCSR.s_org
                      deviceIDCSR.s_country
                      deviceIDCSR.ku
                      l0.deviceID_pub;

  serialize_deviceIDCRI deviceIDCRI deviceIDCRI_len l0.deviceIDCRI_buf;

  fold_l0_perm l0;
  ()
}
```

assume 
val spec_sign_and_finalize_deviceIDCSR
  (deviceID_priv: Seq.seq U8.t)
  (deviceIDCRI_len: U32.t)
  (deviceIDCRI_seq: Seq.seq U8.t)
  // : deviceIDCSR_t deviceIDCRI_len
  : Seq.seq U8.t

```pulse
fn sign_and_finalize_deviceIDCSR
  (l0: l0_record)
  (deviceIDCSR: deviceIDCSR_ingredients_t)
  (#vl0: Ghost.erased l0_repr)
  requires (
    l0_perm l0 vl0 `star`
    pure (
      U32.(0ul <^ vl0.deviceIDCRI_len) /\ 
      valid_deviceIDCSR_ingredients vl0.deviceIDCRI_len /\
      vl0.deviceIDCSR_len == length_of_deviceIDCSR vl0.deviceIDCRI_len
    ))
  ensures (
    exists (vl0_:l0_repr). 
      l0_perm l0 vl0_ **
      pure (
        Seq.equal 
          vl0_.deviceIDCSR_buf
          (spec_serialize_deviceIDCSR vl0.deviceIDCRI_len
                                      (spec_x509_get_deviceIDCSR
                                        vl0.deviceIDCRI_len
                                        vl0_.deviceIDCRI_buf
                                        vl0_.deviceIDCRI_sig))
    ))
{
  admit()
(* 
(* Classify AliasKeyTBS *)
  let deviceIDCRI_buf_sec: B.lbuffer byte_sec (v deviceIDCRI_len) = B.alloca (u8 0x00) deviceIDCRI_len in
  classify_public_buffer
    (* len *) deviceIDCRI_len
    (* src *) deviceIDCRI_buf
    (* dst *) deviceIDCRI_buf_sec;

(* Sign Classified AliasKeyTBS *)
  let deviceIDCRI_sig_sec: B.lbuffer byte_sec 64 = B.alloca (u8 0x00) 64ul in
  Ed25519.sign
    (* sig *) deviceIDCRI_sig_sec
    (* key *) deviceID_priv
    (* len *) deviceIDCRI_len
    (* msg *) deviceIDCRI_buf_sec;

(* Declassify AliasKeyTBS Signature *)
  let deviceIDCRI_sig: B.lbuffer byte_pub 64 = B.alloca 0x00uy 64ul in
  declassify_secret_buffer
    (* len *) 64ul
    (* src *) deviceIDCRI_sig_sec
    (* dst *) deviceIDCRI_sig;

(* Finalize AliasKeyCRT with AliasKeyTBS and Signature *)
  let deviceIDCRI_buf32: B32.lbytes32 deviceIDCRI_len = B32.of_buffer deviceIDCRI_len deviceIDCRI_buf in
  let deviceIDCRI_sig32: x509_signature_raw_t = B32.of_buffer 64ul deviceIDCRI_sig in

  printf "Creating AliasKey Certificate CRT message\n" done;
  let deviceIDCSR: deviceIDCSR_t deviceIDCRI_len = x509_get_deviceIDCSR
                                                             deviceIDCRI_len
                                                             deviceIDCRI_buf32
                                                             deviceIDCRI_sig32 in
  (* Prf *) lemma_serialize_deviceIDCSR_size_exact deviceIDCRI_len deviceIDCSR;

  printf "Serializing AliasKey Certificate CRT\n" done;
(* Serialize AliasKeyCRT *)
  let offset = serialize32_deviceIDCSR_backwards
                 deviceIDCRI_len
                 deviceIDCSR
                 deviceIDCSR_buf
                 deviceIDCSR_len in

  HST.pop_frame ()
*)
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
            vl0.deviceID_pub)
          vl0.deviceIDCRI_len))

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
  create_deviceIDCRI l0 deviceIDCSR;
  
  sign_and_finalize_deviceIDCSR l0 deviceIDCSR;

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
