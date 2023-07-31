module L0Types
open Pulse.Main
open Pulse.Steel.Wrapper
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
open FStar.Ghost
module R = Steel.ST.Reference
module A = Steel.ST.Array
module T = FStar.Tactics
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open Array
open HACL

assume
val x509_version_t : Type0

assume
val x509_serialNumber_t : Type0

assume
val deviceIDCRI_t : Type0

assume
val deviceIDCSR_t (len: US.t) : Type0

assume
val aliasKeyTBS_t : Type0

assume
val aliasKeyCRT_t (len: US.t) : Type0

(* L0 Context *)
noeq
type l0_context = { cdi: A.larray U8.t (US.v dice_digest_len); }

let l0_context_perm (c:l0_context) : vprop
  = exists_ (fun (s:elseq U8.t dice_digest_len) -> A.pts_to c.cdi full_perm s) `star`
    pure (A.is_full_array c.cdi)

let mk_l0_context cdi : l0_context = {cdi}

(* L0 Record *)
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
  A.pts_to record.fwid full_perm repr.fwid `star`
  A.pts_to record.deviceID_label full_perm repr.deviceID_label `star`
  A.pts_to record.aliasKey_label full_perm repr.aliasKey_label `star`
  pure (
    valid_hkdf_lbl_len record.deviceID_label_len /\
    valid_hkdf_lbl_len record.aliasKey_label_len
  )