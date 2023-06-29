module L0Types
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

let elseq (a:Type) (l:nat) = s:Ghost.erased (Seq.seq a) { Seq.length s == l }

assume
val deviceIDCRI_t : Type0

assume
val deviceIDCSR_t (len: U32.t) : Type0

noeq
type deviceIDCSR_ingredients_t = {
  ku: U32.t;
  version: U32.t;
  s_common: string;
  s_org: string;
  s_country: string;
}

assume
val valid_deviceIDCSR_ingredients (len: U32.t) : prop

assume
val x509_version_t : Type0

assume
val x509_serialNumber_t : Type0

noeq
type aliasKeyCRT_ingredients_t = {
  aliasKeyCrt_version: x509_version_t;
  aliasKeyCrt_serialNumber: x509_serialNumber_t;
  // aliasKeyCrt_i_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  // aliasKeyCrt_i_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  // aliasKeyCrt_i_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING;
  // aliasKeyCrt_notBefore: datatype_of_asn1_type UTC_TIME;
  // aliasKeyCrt_notAfter : datatype_of_asn1_type Generalized_Time;
  // aliasKeyCrt_s_common:  x509_RDN_x520_attribute_string_t COMMON_NAME  IA5_STRING;
  // aliasKeyCrt_s_org:     x509_RDN_x520_attribute_string_t ORGANIZATION IA5_STRING;
  // aliasKeyCrt_s_country: x509_RDN_x520_attribute_string_t COUNTRY      PRINTABLE_STRING;
  // aliasKeyCrt_ku: key_usage_payload_t;
  // aliasKeyCrt_l0_version: datatype_of_asn1_type INTEGER;
}

noeq
type l0_record = {
(* Common Inputs *)
  cdi: A.larray U8.t 32; (* secret bytes *)
  fwid: A.larray U8.t 32; (* public bytes *)
  deviceID_label_len: hkdf_lbl_len; (* should be U32 *)
  deviceID_label: A.larray U8.t (US.v deviceID_label_len); (* public bytes *)
  aliasKey_label_len: hkdf_lbl_len; (* should be U32 *)
  aliasKey_label: A.larray U8.t (US.v aliasKey_label_len); (* public bytes *)
(* DeviceID CSR Inputs*)
  deviceIDCSR_ingredients: deviceIDCSR_ingredients_t;
(* AliasKey Crt Inputs*)
  aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t;
(* Common Outputs *)
  deviceID_pub: A.larray U8.t 32; (* public bytes *)
  deviceID_priv: A.larray U8.t 32; (* secret bytes *) (* needed in step1 *)
  aliasKey_pub: A.larray U8.t 32; (* public bytes *)
  aliasKey_priv: A.larray U8.t 32; (* secret bytes *)
(* DeviceID CSR Outputs *)
  deviceIDCSR_len: R.ref U32.t; (* should be U32 *)
  deviceIDCSR_buf: A.array U8.t; (* public bytes *)
(* DeviceID CRI Outputs *)
  deviceIDCRI_len: R.ref U32.t; (* should be U32 *)
  deviceIDCRI_buf: A.array U8.t; (* public bytes *)
  deviceIDCRI_sig: A.array U8.t;
(* AliasKey Crt Outputs *)
  aliasKeyCRT_len: US.t; (* should be U32 *)
  aliasKeyCRT_buf: A.larray U8.t (US.v aliasKeyCRT_len); (* public bytes *)
(* AuthKey Outputs *)
  authKeyID: A.larray U8.t 32;
}

noeq
type l0_repr = {
  cdi: Seq.seq U8.t;
  fwid: Seq.seq U8.t;
  deviceID_label: Seq.seq U8.t;
  aliasKey_label: Seq.seq U8.t;
  deviceID_pub: Seq.seq U8.t;
  deviceID_priv: Seq.seq U8.t;
  aliasKey_pub: Seq.seq U8.t;
  aliasKey_priv: Seq.seq U8.t;
  deviceIDCSR_len: U32.t;
  deviceIDCSR_buf: elseq U8.t (U32.v deviceIDCSR_len);
  deviceIDCRI_len: U32.t;
  deviceIDCRI_buf: elseq U8.t (U32.v deviceIDCRI_len);
  deviceIDCRI_sig: Seq.seq U8.t;
  aliasKeyCRT_buf: Seq.seq U8.t;
  authKeyID: Seq.seq U8.t;
}

let mk_l0_repr cdi fwid deviceID_label aliasKey_label deviceID_pub
               deviceID_priv aliasKey_pub aliasKey_priv
               deviceIDCSR_len deviceIDCSR_buf
               deviceIDCRI_len deviceIDCRI_buf
               deviceIDCRI_sig aliasKeyCRT_buf authKeyID = 

    { cdi; fwid; deviceID_label; aliasKey_label; deviceID_pub;
      deviceID_priv; aliasKey_pub; aliasKey_priv;
      deviceIDCSR_len; deviceIDCSR_buf;
      deviceIDCRI_len; deviceIDCRI_buf;
      deviceIDCRI_sig; aliasKeyCRT_buf; authKeyID }

let l0_perm (l0:l0_record) (vl0: l0_repr) 
            // (#pcdi #pfwid #pdeviceID_label #paliasKey_label: perm)
  : vprop = 
  // A.pts_to l0.cdi pcdi vl0.cdi `star`
  // A.pts_to l0.fwid pfwid vl0.fwid `star`
  // A.pts_to l0.deviceID_label pdeviceID_label vl0.deviceID_label `star`
  // A.pts_to l0.aliasKey_label paliasKey_label vl0.aliasKey_label `star`
  A.pts_to l0.cdi full_perm vl0.cdi `star`
  A.pts_to l0.fwid full_perm vl0.fwid `star`
  A.pts_to l0.deviceID_label full_perm vl0.deviceID_label `star`
  A.pts_to l0.aliasKey_label full_perm vl0.aliasKey_label `star`
  A.pts_to l0.deviceID_pub full_perm vl0.deviceID_pub `star`
  A.pts_to l0.deviceID_priv full_perm vl0.deviceID_priv `star`
  A.pts_to l0.aliasKey_pub full_perm vl0.aliasKey_pub `star`
  A.pts_to l0.aliasKey_priv full_perm vl0.aliasKey_priv `star`
  R.pts_to l0.deviceIDCSR_len full_perm vl0.deviceIDCSR_len `star`
  A.pts_to l0.deviceIDCSR_buf full_perm vl0.deviceIDCSR_buf `star`
  R.pts_to l0.deviceIDCRI_len full_perm vl0.deviceIDCRI_len `star`
  A.pts_to l0.deviceIDCRI_buf full_perm vl0.deviceIDCRI_buf `star`
  A.pts_to l0.deviceIDCRI_sig full_perm vl0.deviceIDCRI_sig `star`
  A.pts_to l0.aliasKeyCRT_buf full_perm vl0.aliasKeyCRT_buf `star`
  A.pts_to l0.authKeyID full_perm vl0.authKeyID

```pulse
ghost
fn fold_l0_perm (l0:l0_record)
                (#cdi #fwid #deviceID_label #aliasKey_label #deviceID_pub
                 #deviceID_priv #aliasKey_pub #aliasKey_priv:erased (Seq.seq U8.t))
                (#deviceIDCSR_len:erased U32.t)
                (#deviceIDCSR_buf:elseq U8.t (U32.v deviceIDCSR_len))
                (#deviceIDCRI_len:erased U32.t)
                (#deviceIDCRI_buf:elseq U8.t (U32.v deviceIDCRI_len))
                (#deviceIDCRI_sig #aliasKeyCRT_buf #authKeyID: erased (Seq.seq U8.t))
  requires
    A.pts_to l0.cdi full_perm cdi `star`
    A.pts_to l0.fwid full_perm fwid `star`
    A.pts_to l0.deviceID_label full_perm deviceID_label `star`
    A.pts_to l0.aliasKey_label full_perm aliasKey_label `star`
    A.pts_to l0.deviceID_pub full_perm deviceID_pub `star`
    A.pts_to l0.deviceID_priv full_perm deviceID_priv `star`
    A.pts_to l0.aliasKey_pub full_perm aliasKey_pub `star`
    A.pts_to l0.aliasKey_priv full_perm aliasKey_priv `star`
    R.pts_to l0.deviceIDCSR_len full_perm deviceIDCSR_len `star`
    A.pts_to l0.deviceIDCSR_buf full_perm deviceIDCSR_buf `star`
    R.pts_to l0.deviceIDCRI_len full_perm deviceIDCRI_len `star`
    A.pts_to l0.deviceIDCRI_buf full_perm deviceIDCRI_buf `star`
    A.pts_to l0.deviceIDCRI_sig full_perm deviceIDCRI_sig `star`
    A.pts_to l0.aliasKeyCRT_buf full_perm aliasKeyCRT_buf `star`
    A.pts_to l0.authKeyID full_perm authKeyID
  ensures
    l0_perm l0 (mk_l0_repr cdi fwid deviceID_label aliasKey_label deviceID_pub
                           deviceID_priv aliasKey_pub aliasKey_priv
                           deviceIDCSR_len deviceIDCSR_buf
                           deviceIDCRI_len deviceIDCRI_buf
                           deviceIDCRI_sig aliasKeyCRT_buf authKeyID)
{
   fold (l0_perm l0 (mk_l0_repr cdi fwid deviceID_label aliasKey_label deviceID_pub
                           deviceID_priv aliasKey_pub aliasKey_priv
                           deviceIDCSR_len deviceIDCSR_buf
                           deviceIDCRI_len deviceIDCRI_buf
                           deviceIDCRI_sig aliasKeyCRT_buf authKeyID))
}
```


// assume
// val l0_perm (l0:l0_record) (vl0: l0_repr) : vprop

// assume
// val l0_perm_definition (l0:l0_record) (vl0: l0_repr)
//   : Lemma 
//     (ensures l0_perm l0 vl0 === l0_perm' l0 vl0)
//     [SMTPat (l0_perm l0 vl0)]

assume 
val u32_to_us (v:U32.t) : US.t
