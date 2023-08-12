module L0Core
open L0Types
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module SZ = FStar.SizeT
open HACL
open X509

// Needs to be exposed so that the caller of l0_main can prove that they
// computed deviceIDCSR_len correctly
let deviceIDCSR_pre
  (deviceIDCSR: deviceIDCSR_ingredients_t) 
  (deviceIDCRI_len: SZ.t) 
  (deviceIDCSR_len: SZ.t) 
  = deviceIDCRI_len == len_of_deviceIDCRI
                        deviceIDCSR.version
                        deviceIDCSR.s_common
                        deviceIDCSR.s_org
                        deviceIDCSR.s_country /\
    0 < SZ.v deviceIDCRI_len /\ 
    valid_deviceIDCSR_ingredients deviceIDCRI_len /\
    deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len

// Needs to be exposed so that the caller of l0_main can prove that they
// computed aliasKeyCRT_len correctly
let aliasKeyCRT_pre
  (aliasKeyCRT:aliasKeyCRT_ingredients_t) 
  (aliasKeyTBS_len:SZ.t) 
  (aliasKeyCRT_len:SZ.t) 
  = aliasKeyTBS_len == len_of_aliasKeyTBS
                        aliasKeyCRT.serialNumber
                        aliasKeyCRT.i_common
                        aliasKeyCRT.i_org
                        aliasKeyCRT.i_country
                        aliasKeyCRT.s_common
                        aliasKeyCRT.s_org
                        aliasKeyCRT.s_country
                        aliasKeyCRT.l0_version /\
    0 < SZ.v aliasKeyTBS_len /\ 
    valid_aliasKeyCRT_ingredients aliasKeyTBS_len /\
    aliasKeyCRT_len == length_of_aliasKeyCRT aliasKeyTBS_len

val aliasKey_functional_correctness 
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi:Seq.seq U8.t)
  (fwid:Seq.seq U8.t)
  (aliasKey_label_len:hkdf_lbl_len)
  (aliasKey_label:Seq.seq U8.t)
  (aliasKey_pub:elseq U8.t v32us)
  (aliasKey_priv:elseq U8.t v32us)
  : prop

val deviceIDCSR_functional_correctness
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi: Seq.seq U8.t)
  (deviceID_label_len: hkdf_lbl_len)
  (deviceID_label: Seq.seq U8.t)
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  (deviceIDCSR_len: SZ.t)
  (deviceIDCSR_buf: elseq U8.t deviceIDCSR_len)
  : prop

val aliasKeyCRT_functional_correctness
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi:Seq.seq U8.t)
  (fwid:Seq.seq U8.t)
  (deviceID_label_len:hkdf_lbl_len)
  (deviceID_label:Seq.seq U8.t)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (aliasKeyCRT_len:SZ.t)
  (aliasKeyCRT_buf:elseq U8.t aliasKeyCRT_len)
  (aliasKey_pub:elseq U8.t v32us)
  : prop

val l0_main
  (cdi: A.larray U8.t (SZ.v dice_digest_len))
  (deviceID_pub: A.larray U8.t (SZ.v v32us))
  (deviceID_priv: A.larray U8.t (SZ.v v32us))
  (aliasKey_pub: A.larray U8.t (SZ.v v32us))
  (aliasKey_priv: A.larray U8.t (SZ.v v32us))
  (aliasKeyTBS_len:SZ.t)
  (aliasKeyCRT_len:SZ.t)
  (aliasKeyCRT: A.larray U8.t (SZ.v aliasKeyCRT_len))
  (deviceIDCRI_len:SZ.t)
  (deviceIDCSR_len:SZ.t)
  (deviceIDCSR: A.larray U8.t (SZ.v deviceIDCSR_len))
  (record: l0_record_t)
  (#repr: erased l0_record_repr)
  (#p:perm)
  (#cdi0:erased (elseq U8.t dice_digest_len))
  (#deviceID_pub0 #deviceID_priv0 #aliasKey_pub0 #aliasKey_priv0:erased (elseq U8.t v32us)) 
  (#aliasKeyCRT0: elseq U8.t aliasKeyCRT_len)
  (#deviceIDCSR0: elseq U8.t deviceIDCSR_len)
  : stt unit (l0_record_perm record repr **
              A.pts_to cdi p cdi0 **
              A.pts_to deviceID_pub full_perm deviceID_pub0 **
              A.pts_to deviceID_priv full_perm deviceID_priv0 **
              A.pts_to aliasKey_pub full_perm aliasKey_pub0 **
              A.pts_to aliasKey_priv full_perm aliasKey_priv0 **
              A.pts_to aliasKeyCRT full_perm aliasKeyCRT0 **
              A.pts_to deviceIDCSR full_perm deviceIDCSR0 **
              pure (deviceIDCSR_pre record.deviceIDCSR_ingredients deviceIDCRI_len deviceIDCSR_len
                 /\ aliasKeyCRT_pre record.aliasKeyCRT_ingredients aliasKeyTBS_len aliasKeyCRT_len))
             (fun _ -> 
              l0_record_perm record repr **
              A.pts_to cdi p cdi0 **
              exists_ (fun (deviceID_pub1:elseq U8.t v32us) ->
              exists_ (fun (deviceID_priv1:elseq U8.t v32us) -> 
              exists_ (fun (aliasKey_pub1:elseq U8.t v32us) ->
              exists_ (fun (aliasKey_priv1:elseq U8.t v32us) ->
              exists_ (fun (aliasKeyCRT1:elseq U8.t aliasKeyCRT_len) ->
              exists_ (fun (deviceIDCSR1:elseq U8.t deviceIDCSR_len) ->
                A.pts_to deviceID_pub full_perm deviceID_pub1 **
                A.pts_to deviceID_priv full_perm deviceID_priv1 **
                A.pts_to aliasKey_pub full_perm aliasKey_pub1 **
                A.pts_to aliasKey_priv full_perm aliasKey_priv1 **
                A.pts_to aliasKeyCRT full_perm aliasKeyCRT1 **
                A.pts_to deviceIDCSR full_perm deviceIDCSR1 **
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
                    aliasKeyCRT_len aliasKeyCRT1 aliasKey_pub1))))))))