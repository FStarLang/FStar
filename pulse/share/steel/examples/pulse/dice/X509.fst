module X509
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

assume
val length_of_deviceIDCSR (len: U32.t) : U32.t 

assume
val len_of_deviceIDCRI
  (version: U32.t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  : U32.t

assume
val spec_serialize_deviceIDCSR 
  (deviceIDCRI_len: U32.t)
  (deviceIDCSR: deviceIDCSR_t deviceIDCRI_len)
  : Seq.seq U8.t

assume
val serialize_deviceIDCSR 
  (deviceIDCRI_len: U32.t)
  (deviceIDCSR: deviceIDCSR_t deviceIDCRI_len)
  : Seq.seq U8.t

assume
val spec_serialize_deviceIDCRI
  (deviceIDCRI: deviceIDCRI_t)
  (deviceIDCRI_len: U32.t)
  : elseq U8.t (U32.v deviceIDCRI_len)

assume
val serialize_deviceIDCRI
  (deviceIDCRI: deviceIDCRI_t)
  (deviceIDCRI_len: U32.t)
  (deviceIDCRI_buf: A.array U8.t)
  (#deviceIDCRI_buf0: Ghost.erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to deviceIDCRI_buf full_perm deviceIDCRI_buf0)
    (fun _ -> A.pts_to deviceIDCRI_buf full_perm (spec_serialize_deviceIDCRI deviceIDCRI deviceIDCRI_len))

assume 
val spec_x509_get_deviceIDCRI
  (version: U32.t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  (ku: U32.t)
  (deviceID_pub: Seq.seq U8.t)
  : deviceIDCRI_t

assume 
val x509_get_deviceIDCRI
  (version: U32.t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  (ku: U32.t)
  (deviceID_pub: A.array U8.t)
  (#deviceID_pub0: Ghost.erased (Seq.seq U8.t))
  : stt deviceIDCRI_t
    (A.pts_to deviceID_pub full_perm deviceID_pub0)
    (fun res -> 
      A.pts_to deviceID_pub full_perm deviceID_pub0 `star`
      pure (res == spec_x509_get_deviceIDCRI version s_common s_org s_country ku deviceID_pub0))

assume 
val spec_x509_get_deviceIDCSR
  (deviceIDCRI_len: U32.t)
  (deviceIDCRI_buf: Seq.seq U8.t)
  (deviceIDCRI_sig: Seq.seq U8.t)
  : deviceIDCSR_t deviceIDCRI_len
