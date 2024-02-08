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
open L0Types
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module U8 = FStar.UInt8
module SZ = FStar.SizeT
open HACL
open X509

// Needs to be exposed so that the caller of l0_main can prove that they
// computed deviceIDCSR_len correctly
noextract
let deviceIDCSR_pre
  (deviceIDCSR: deviceIDCSR_ingredients_t) 
  (deviceIDCRI_len: SZ.t) 
  (deviceIDCSR_len: SZ.t) 
  = deviceIDCRI_len == snd (len_of_deviceIDCRI deviceIDCSR) /\
    0 < SZ.v deviceIDCRI_len /\ 
    valid_deviceIDCSR_ingredients deviceIDCRI_len /\
    deviceIDCSR_len == length_of_deviceIDCSR deviceIDCRI_len

// Needs to be exposed so that the caller of l0_main can prove that they
// computed aliasKeyCRT_len correctly
noextract
let aliasKeyCRT_pre
  (aliasKeyCRT:aliasKeyCRT_ingredients_t) 
  (aliasKeyTBS_len:SZ.t) 
  (aliasKeyCRT_len:SZ.t) 
  = aliasKeyTBS_len == snd (len_of_aliasKeyTBS aliasKeyCRT) /\
    0 < SZ.v aliasKeyTBS_len /\ 
    valid_aliasKeyCRT_ingredients aliasKeyTBS_len /\
    aliasKeyCRT_len == length_of_aliasKeyCRT aliasKeyTBS_len

noextract
val aliasKey_functional_correctness 
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi:Seq.seq U8.t)
  (fwid:Seq.seq U8.t)
  (aliasKey_label_len:hkdf_lbl_len)
  (aliasKey_label:Seq.seq U8.t)
  (aliasKey_pub:Seq.seq U8.t)
  (aliasKey_priv:Seq.seq U8.t)
  : prop

noextract
val deviceIDCSR_functional_correctness
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi: Seq.seq U8.t)
  (deviceID_label_len: hkdf_lbl_len)
  (deviceID_label: Seq.seq U8.t)
  (deviceIDCSR_ingredients: deviceIDCSR_ingredients_t)
  (deviceIDCSR_len: SZ.t)
  (deviceIDCSR_buf: Seq.seq U8.t)
  : prop

noextract
val aliasKeyCRT_functional_correctness
  (alg:alg_t)
  (dig_len:hkdf_ikm_len)
  (cdi:Seq.seq U8.t)
  (fwid:Seq.seq U8.t)
  (deviceID_label_len:hkdf_lbl_len)
  (deviceID_label:Seq.seq U8.t)
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (aliasKeyCRT_len:SZ.t)
  (aliasKeyCRT_buf:Seq.seq U8.t)
  (aliasKey_pub:Seq.seq U8.t)
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
  (#repr: erased l0_record_repr_t)
  (#cdi0 #deviceID_pub0 #deviceID_priv0 #aliasKey_pub0 #aliasKey_priv0 #aliasKeyCRT0 #deviceIDCSR0: erased (Seq.seq U8.t))
  (#cdi_perm #p:perm)
  : stt l0_record_t
             (l0_record_perm record p repr **
              A.pts_to cdi #cdi_perm cdi0 **
              A.pts_to deviceID_pub deviceID_pub0 **
              A.pts_to deviceID_priv deviceID_priv0 **
              A.pts_to aliasKey_pub aliasKey_pub0 **
              A.pts_to aliasKey_priv aliasKey_priv0 **
              A.pts_to aliasKeyCRT aliasKeyCRT0 **
              A.pts_to deviceIDCSR deviceIDCSR0 **
              pure (deviceIDCSR_pre record.deviceIDCSR_ingredients deviceIDCRI_len deviceIDCSR_len
                 /\ aliasKeyCRT_pre record.aliasKeyCRT_ingredients aliasKeyTBS_len aliasKeyCRT_len))
             (fun record -> 
              l0_record_perm record p repr **
              A.pts_to cdi #cdi_perm cdi0 **
              (exists* (deviceID_pub1
                        deviceID_priv1
                        aliasKey_pub1
                        aliasKey_priv1
                        aliasKeyCRT1
                        deviceIDCSR1:Seq.seq U8.t).
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
                    aliasKeyCRT_len aliasKeyCRT1 aliasKey_pub1)))