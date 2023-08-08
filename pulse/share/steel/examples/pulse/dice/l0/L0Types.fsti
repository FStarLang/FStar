module L0Types
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open HACL

val x509_version_t : Type0

val x509_serialNumber_t : Type0

val deviceIDCRI_t : Type0

val deviceIDCSR_t (len: US.t) : Type0

val aliasKeyTBS_t : Type0

val aliasKeyCRT_t (len: US.t) : Type0

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

noeq
type l0_record_t = {
  fwid: A.larray U8.t (US.v v32us);
  deviceID_label_len: hkdf_lbl_len;
  deviceID_label: A.larray U8.t (US.v deviceID_label_len); (* public bytes *)
  aliasKey_label_len: hkdf_lbl_len;
  aliasKey_label: A.larray U8.t (US.v aliasKey_label_len); (* public bytes *)
  deviceIDCSR_ingredients: deviceIDCSR_ingredients_t;
  aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t;
}

noeq
type l0_record_repr = {
  fwid: Seq.seq U8.t;
  deviceID_label: Seq.seq U8.t;
  aliasKey_label: Seq.seq U8.t;
}

let mk_l0_repr fwid deviceID_label aliasKey_label
  = {fwid; deviceID_label; aliasKey_label}

let l0_record_perm (record:l0_record_t) (repr:l0_record_repr) : vprop =
  A.pts_to record.fwid full_perm repr.fwid **
  A.pts_to record.deviceID_label full_perm repr.deviceID_label **
  A.pts_to record.aliasKey_label full_perm repr.aliasKey_label **
  pure (
    valid_hkdf_lbl_len record.deviceID_label_len /\
    valid_hkdf_lbl_len record.aliasKey_label_len
  )