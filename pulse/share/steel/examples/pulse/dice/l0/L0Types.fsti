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

module L0Types
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module V = Pulse.Lib.Vec
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open HACL

val x509_version_t : Type0

val x509_serialNumber_t : Type0

val deviceIDCRI_t : Type0

val deviceIDCSR_t : Type0

val aliasKeyTBS_t : Type0

val aliasKeyCRT_t : Type0

noeq
type deviceIDCSR_ingredients_t = {
  ku        : U32.t;
  version   : x509_version_t;
  s_common  : string;
  s_org     : string;
  s_country : string;
}

noeq
type aliasKeyCRT_ingredients_t = {
  version       : x509_version_t;
  serialNumber  : x509_serialNumber_t;
  i_common      : string;
  i_org         : string;
  i_country     : string;
  notBefore     : US.t; (* UTC_TIME *)
  notAfter      : US.t; (* Generalized_Time *)
  s_common      : string;
  s_org         : string;
  s_country     : string;
  ku            : U32.t;
  l0_version    : U32.t;
}

(* Record *)
noeq
type l0_record_t = {
  fwid: V.lvec U8.t (US.v v32us);
  deviceID_label_len: hkdf_lbl_len;
  deviceID_label: V.lvec U8.t (US.v deviceID_label_len); (* public bytes *)
  aliasKey_label_len: hkdf_lbl_len;
  aliasKey_label: V.lvec U8.t (US.v aliasKey_label_len); (* public bytes *)
  deviceIDCSR_ingredients: deviceIDCSR_ingredients_t;
  aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t;
}

noeq
type l0_record_repr_t = {
  fwid: Seq.seq U8.t;
  deviceID_label: Seq.seq U8.t;
  aliasKey_label: Seq.seq U8.t;
}

let mk_l0_repr fwid deviceID_label aliasKey_label
  = {fwid; deviceID_label; aliasKey_label}

// don't need full perm
let l0_record_perm (record:l0_record_t) (p:perm) (repr:l0_record_repr_t) : vprop =
  V.pts_to record.fwid #p repr.fwid **
  V.pts_to record.deviceID_label #p repr.deviceID_label **
  V.pts_to record.aliasKey_label #p repr.aliasKey_label **
  pure (
    valid_hkdf_lbl_len record.deviceID_label_len /\
    valid_hkdf_lbl_len record.aliasKey_label_len
  )