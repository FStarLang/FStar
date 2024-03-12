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

module X509
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open HACL
open L0Types

assume
val valid_deviceIDCSR_ingredients (len: US.t) : prop

assume
val valid_deviceIDCSR_ingredients_elim (len: US.t) : Lemma
  (requires (valid_deviceIDCSR_ingredients len))
  (ensures (US.v len < pow2 32)) // constrained by HACL.ed25519_sign
  [SMTPat (valid_deviceIDCSR_ingredients len)]

assume
val valid_aliasKeyCRT_ingredients (len: US.t) : prop

assume
val valid_aliasKeyCRT_ingredients_elim (len: US.t) : Lemma
  (requires (valid_aliasKeyCRT_ingredients len))
  (ensures (US.v len < pow2 32)) // constrained by HACL.ed25519_sign
  [SMTPat (valid_aliasKeyCRT_ingredients len)]

assume
val length_of_deviceIDCSR (len: US.t) : US.t 

assume
val length_of_aliasKeyCRT (len: US.t) : US.t 

assume
val len_of_deviceIDCRI (x:deviceIDCSR_ingredients_t)
  : tuple2 (y:deviceIDCSR_ingredients_t { y == x })
           (v:US.t{0 < US.v v /\ valid_deviceIDCSR_ingredients v})

assume
val len_of_aliasKeyTBS (x:aliasKeyCRT_ingredients_t)
  : tuple2 (y:aliasKeyCRT_ingredients_t { y == x})
           (v:US.t{0 < US.v v /\ valid_aliasKeyCRT_ingredients v})

(* Serialize Functions *)

assume
val spec_serialize_deviceIDCRI
  (deviceIDCRI: deviceIDCRI_t)
  (deviceIDCRI_len: US.t)
  : GTot (Seq.seq U8.t)

assume
val serialize_deviceIDCRI
  (deviceIDCRI: deviceIDCRI_t)
  (deviceIDCRI_len: US.t)
  (deviceIDCRI_buf: A.larray U8.t (US.v deviceIDCRI_len))
  (#deviceIDCRI_buf0: erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to deviceIDCRI_buf deviceIDCRI_buf0)
    (fun _ -> A.pts_to deviceIDCRI_buf (spec_serialize_deviceIDCRI 
                                                    deviceIDCRI 
                                                    deviceIDCRI_len))

assume
val spec_serialize_deviceIDCSR 
  (deviceIDCRI_len: US.t)
  (deviceIDCSR_len: US.t)
  (deviceIDCSR: deviceIDCSR_t)
  : GTot (Seq.seq U8.t)

assume
val serialize_deviceIDCSR 
  (deviceIDCRI_len: US.t)
  (deviceIDCSR: deviceIDCSR_t)
  (deviceIDCSR_len: US.t)
  (deviceIDCSR_buf: A.larray U8.t (US.v deviceIDCSR_len))
  (#_buf:erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to deviceIDCSR_buf _buf)
    (fun _ -> A.pts_to deviceIDCSR_buf (spec_serialize_deviceIDCSR 
                                                    deviceIDCRI_len 
                                                    deviceIDCSR_len 
                                                    deviceIDCSR))

assume
val spec_serialize_aliasKeyTBS
  (aliasKeyTBS: aliasKeyTBS_t)
  (aliasKeyTBS_len: US.t)
  : GTot (Seq.seq U8.t)

assume
val serialize_aliasKeyTBS
  (aliasKeyTBS: aliasKeyTBS_t)
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: A.larray U8.t (US.v aliasKeyTBS_len))
  (#aliasKeyTBS_buf0: erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to aliasKeyTBS_buf aliasKeyTBS_buf0)
    (fun _ -> A.pts_to aliasKeyTBS_buf (spec_serialize_aliasKeyTBS 
                                                   aliasKeyTBS 
                                                   aliasKeyTBS_len))

assume
val spec_serialize_aliasKeyCRT
  (aliasKeyTBS_len: US.t)
  (aliasKeyCRT_len: US.t)
  (aliasKeyCRT: aliasKeyCRT_t)
  : GTot (Seq.seq U8.t)

assume  
val serialize_aliasKeyCRT
  (aliasKeyTBS_len: US.t)
  (aliasKeyCRT: aliasKeyCRT_t)
  (aliasKeyCRT_len: US.t)
  (aliasKeyCRT_buf: A.larray U8.t (US.v aliasKeyCRT_len))
  (#_buf:erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to aliasKeyCRT_buf _buf)
    (fun _ -> A.pts_to aliasKeyCRT_buf (spec_serialize_aliasKeyCRT 
                                                    aliasKeyTBS_len 
                                                    aliasKeyCRT_len 
                                                    aliasKeyCRT))

(* Get Functions *)

assume 
val spec_x509_get_deviceIDCSR
  (deviceIDCRI_len: US.t)
  (deviceIDCRI_buf: Seq.seq U8.t)
  (deviceIDCRI_sig: Seq.seq U8.t)
  : GTot deviceIDCSR_t

assume 
val x509_get_deviceIDCSR
  (deviceIDCRI_len: US.t)
  (deviceIDCRI_buf: A.larray U8.t (US.v deviceIDCRI_len))
  (deviceIDCRI_sig: A.array U8.t)
  (#buf_perm #sig_perm:perm)
  (#buf #sig:erased (Seq.seq U8.t))
  : stt deviceIDCSR_t
    (A.pts_to deviceIDCRI_buf #buf_perm buf **
     A.pts_to deviceIDCRI_sig #sig_perm sig)
     (fun res -> 
        A.pts_to deviceIDCRI_buf #buf_perm buf **
        A.pts_to deviceIDCRI_sig #sig_perm sig **
        pure (res == spec_x509_get_deviceIDCSR 
                      deviceIDCRI_len 
                      buf sig))

assume 
val spec_x509_get_deviceIDCRI
  (version: x509_version_t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  (ku: U32.t)
  (deviceID_pub: Seq.seq U8.t)
  : GTot deviceIDCRI_t

assume 
val x509_get_deviceIDCRI (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (#pub_perm:perm)
  (#deviceID_pub0: erased (Seq.seq U8.t))
  : stt (deviceIDCSR_ingredients_t & deviceIDCRI_t)
    (A.pts_to deviceID_pub #pub_perm deviceID_pub0)
    (fun res -> 
      A.pts_to deviceID_pub #pub_perm deviceID_pub0 **
      pure (fst res == deviceIDCSR_ingredients /\
            snd res == spec_x509_get_deviceIDCRI 
                       deviceIDCSR_ingredients.version
                       deviceIDCSR_ingredients.s_common 
                       deviceIDCSR_ingredients.s_org deviceIDCSR_ingredients.s_country 
                       deviceIDCSR_ingredients.ku deviceID_pub0))

assume 
val spec_x509_get_aliasKeyTBS
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (fwid:Seq.seq U8.t)
  (deviceID_pub aliasKey_pub:Seq.seq U8.t)
  : GTot aliasKeyTBS_t

assume
val x509_get_aliasKeyTBS
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (fwid:A.larray U8.t 32)
  (deviceID_pub:A.larray U8.t (US.v v32us))
  (aliasKey_pub:A.larray U8.t (US.v v32us))
  (#fwid_perm #deviceID_perm #aliasKey_perm:perm)
  (#fwid0 #deviceID0 #aliasKey0:erased (Seq.seq U8.t))
  : stt (aliasKeyCRT_ingredients_t & aliasKeyTBS_t)
  (A.pts_to fwid #fwid_perm fwid0 **
   A.pts_to deviceID_pub #deviceID_perm deviceID0 **
   A.pts_to aliasKey_pub #aliasKey_perm aliasKey0)
  (fun res ->
    A.pts_to fwid #fwid_perm fwid0 **
    A.pts_to deviceID_pub #deviceID_perm deviceID0 **
    A.pts_to aliasKey_pub #aliasKey_perm aliasKey0 **
    pure (fst res == aliasKeyCRT_ingredients /\
          snd res == spec_x509_get_aliasKeyTBS 
                     aliasKeyCRT_ingredients 
                     fwid0 deviceID0 aliasKey0))
  
assume 
val spec_x509_get_aliasKeyCRT
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: Seq.seq U8.t)
  (aliasKeyTBS_sig: Seq.seq U8.t)
  : GTot (aliasKeyCRT_t)

assume 
val x509_get_aliasKeyCRT
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: A.larray U8.t (US.v aliasKeyTBS_len))
  (aliasKeyTBS_sig: A.array U8.t)
  (#buf_perm #sig_perm:perm)
  (#buf #sig:erased (Seq.seq U8.t))
  : stt (aliasKeyCRT_t)
    (A.pts_to aliasKeyTBS_buf #buf_perm buf **
     A.pts_to aliasKeyTBS_sig #sig_perm sig)
     (fun res -> 
        A.pts_to aliasKeyTBS_buf #buf_perm buf **
        A.pts_to aliasKeyTBS_sig #sig_perm sig **
        pure (res == spec_x509_get_aliasKeyCRT 
                      aliasKeyTBS_len 
                      buf sig))
