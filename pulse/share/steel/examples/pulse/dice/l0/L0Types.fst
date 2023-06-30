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
open HACL

let elseq (a:Type) (l:nat) = s:Ghost.erased (Seq.seq a) { Seq.length s == l }

assume
val x509_version_t : Type0

assume
val x509_serialNumber_t : Type0

assume
val deviceIDCRI_t : Type0

assume
val deviceIDCSR_t (len: U32.t) : Type0

assume
val aliasKeyTBS_t : Type0

assume
val aliasKeyCRT_t (len: U32.t) : Type0

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
  aliasKeyTBS_len: R.ref U32.t; (* should be U32 *)
  aliasKeyTBS_buf: A.array U8.t; (* public bytes *)
  aliasKeyCRT_len: R.ref U32.t; (* should be U32 *)
  aliasKeyCRT_buf: A.array U8.t; (* public bytes *)
(* AuthKey Outputs *)
  authKeyID: A.larray U8.t (US.v dice_digest_len);
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
  deviceIDCSR_buf: Seq.seq U8.t;
  deviceIDCRI_len: U32.t;
  deviceIDCRI_buf: Seq.seq U8.t;
  deviceIDCRI_sig: Seq.seq U8.t;
  aliasKeyTBS_len: U32.t;
  aliasKeyTBS_buf: Seq.seq U8.t;
  aliasKeyCRT_len: U32.t;
  aliasKeyCRT_buf: Seq.seq U8.t;
  authKeyID: Seq.seq U8.t;
}

let mk_l0_repr cdi fwid deviceID_label aliasKey_label deviceID_pub
               deviceID_priv aliasKey_pub aliasKey_priv
               deviceIDCSR_len deviceIDCSR_buf
               deviceIDCRI_len deviceIDCRI_buf deviceIDCRI_sig 
               aliasKeyTBS_len aliasKeyTBS_buf 
               aliasKeyCRT_len aliasKeyCRT_buf 
               authKeyID = 
    { cdi; fwid; deviceID_label; aliasKey_label; deviceID_pub;
      deviceID_priv; aliasKey_pub; aliasKey_priv;
      deviceIDCSR_len; deviceIDCSR_buf;
      deviceIDCRI_len; deviceIDCRI_buf; deviceIDCRI_sig; 
      aliasKeyTBS_len; aliasKeyTBS_buf; 
      aliasKeyCRT_len; aliasKeyCRT_buf; 
      authKeyID }

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
  R.pts_to l0.aliasKeyTBS_len full_perm vl0.aliasKeyTBS_len `star`
  A.pts_to l0.aliasKeyTBS_buf full_perm vl0.aliasKeyTBS_buf `star`
  R.pts_to l0.aliasKeyCRT_len full_perm vl0.aliasKeyCRT_len `star`
  A.pts_to l0.aliasKeyCRT_buf full_perm vl0.aliasKeyCRT_buf `star`
  A.pts_to l0.authKeyID full_perm vl0.authKeyID

```pulse
ghost
fn fold_l0_perm (l0:l0_record)
                (#cdi #fwid #deviceID_label #aliasKey_label #deviceID_pub
                 #deviceID_priv #aliasKey_pub #aliasKey_priv:erased (Seq.seq U8.t))
                (#deviceIDCSR_len #deviceIDCRI_len #aliasKeyTBS_len #aliasKeyCRT_len:erased U32.t)
                (#deviceIDCSR_buf #deviceIDCRI_buf #deviceIDCRI_sig #aliasKeyTBS_buf #aliasKeyCRT_buf #authKeyID: erased (Seq.seq U8.t))
  requires
    A.pts_to l0.cdi full_perm cdi **
    A.pts_to l0.fwid full_perm fwid **
    A.pts_to l0.deviceID_label full_perm deviceID_label **
    A.pts_to l0.aliasKey_label full_perm aliasKey_label **
    A.pts_to l0.deviceID_pub full_perm deviceID_pub **
    A.pts_to l0.deviceID_priv full_perm deviceID_priv **
    A.pts_to l0.aliasKey_pub full_perm aliasKey_pub **
    A.pts_to l0.aliasKey_priv full_perm aliasKey_priv **
    R.pts_to l0.deviceIDCSR_len full_perm deviceIDCSR_len **
    A.pts_to l0.deviceIDCSR_buf full_perm deviceIDCSR_buf **
    R.pts_to l0.deviceIDCRI_len full_perm deviceIDCRI_len **
    A.pts_to l0.deviceIDCRI_buf full_perm deviceIDCRI_buf **
    A.pts_to l0.deviceIDCRI_sig full_perm deviceIDCRI_sig **
    R.pts_to l0.aliasKeyTBS_len full_perm aliasKeyTBS_len **
    A.pts_to l0.aliasKeyTBS_buf full_perm aliasKeyTBS_buf **
    R.pts_to l0.aliasKeyCRT_len full_perm aliasKeyCRT_len **
    A.pts_to l0.aliasKeyCRT_buf full_perm aliasKeyCRT_buf **
    A.pts_to l0.authKeyID full_perm authKeyID
  ensures
    l0_perm l0 (mk_l0_repr cdi fwid deviceID_label aliasKey_label deviceID_pub
                           deviceID_priv aliasKey_pub aliasKey_priv
                           deviceIDCSR_len deviceIDCSR_buf
                           deviceIDCRI_len deviceIDCRI_buf deviceIDCRI_sig 
                           aliasKeyTBS_len aliasKeyTBS_buf
                           aliasKeyCRT_len aliasKeyCRT_buf 
                           authKeyID)
{
   fold (l0_perm l0 (mk_l0_repr cdi fwid deviceID_label aliasKey_label deviceID_pub
                           deviceID_priv aliasKey_pub aliasKey_priv
                           deviceIDCSR_len deviceIDCSR_buf
                           deviceIDCRI_len deviceIDCRI_buf deviceIDCRI_sig 
                           aliasKeyTBS_len aliasKeyTBS_buf
                           aliasKeyCRT_len aliasKeyCRT_buf 
                           authKeyID))
}
```

assume 
val u32_to_us (v:U32.t) : US.t
