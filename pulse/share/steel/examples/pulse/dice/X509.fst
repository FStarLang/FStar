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
val valid_deviceIDCSR_ingredients (len: U32.t) : prop

assume
val valid_aliasKeyCRT_ingredients (len: U32.t) : prop

assume
val length_of_deviceIDCSR (len: U32.t) : U32.t 

assume
val length_of_aliasKeyCRT (len: U32.t) : U32.t 

assume
val len_of_deviceIDCRI
  (version: x509_version_t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  : U32.t

assume
val len_of_aliasKeyTBS
  (serialNumber  : x509_serialNumber_t)
  (i_common      : string)
  (i_org         : string)
  (i_country     : string)
  (s_common      : string)
  (s_org         : string)
  (s_country     : string)
  (l0_version    : U32.t)
  : U32.t

(* Serialize Functions *)

assume
val spec_serialize_deviceIDCRI
  (deviceIDCRI: deviceIDCRI_t)
  (deviceIDCRI_len: U32.t)
  : Seq.seq U8.t

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
val spec_serialize_deviceIDCSR 
  (deviceIDCRI_len: U32.t)
  (deviceIDCSR_len: U32.t)
  (deviceIDCSR: deviceIDCSR_t deviceIDCRI_len)
  : Seq.seq U8.t

assume
val serialize_deviceIDCSR 
  (deviceIDCRI_len: U32.t)
  (deviceIDCSR: deviceIDCSR_t deviceIDCRI_len)
  (deviceIDCSR_buf: A.array U8.t)
  (deviceIDCSR_len: U32.t)
  (#_buf:Ghost.erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to deviceIDCSR_buf full_perm _buf)
    (fun _ -> A.pts_to deviceIDCSR_buf full_perm (spec_serialize_deviceIDCSR deviceIDCRI_len deviceIDCSR_len deviceIDCSR))

assume
val spec_serialize_aliasKeyTBS
  (aliasKeyTBS: aliasKeyTBS_t)
  (aliasKeyTBS_len: U32.t)
  : Seq.seq U8.t

assume
val serialize_aliasKeyTBS
  (aliasKeyTBS: aliasKeyTBS_t)
  (aliasKeyTBS_len: U32.t)
  (aliasKeyTBS_buf: A.array U8.t)
  (#aliasKeyTBS_buf0: Ghost.erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to aliasKeyTBS_buf full_perm aliasKeyTBS_buf0)
    (fun _ -> A.pts_to aliasKeyTBS_buf full_perm (spec_serialize_aliasKeyTBS aliasKeyTBS aliasKeyTBS_len))

assume
val spec_serialize_aliasKeyCRT
  (aliasKeyTBS_len: U32.t)
  (aliasKeyCRT_len: U32.t)
  (aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len)
  : Seq.seq U8.t

assume
val serialize_aliasKeyCRT
  (aliasKeyTBS_len: U32.t)
  (aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len)
  (aliasKeyCRT_buf: A.array U8.t)
  (aliasKeyCRT_len: U32.t)
  (#_buf:Ghost.erased (Seq.seq U8.t))
  : stt unit
    (A.pts_to aliasKeyCRT_buf full_perm _buf)
    (fun _ -> A.pts_to aliasKeyCRT_buf full_perm (spec_serialize_aliasKeyCRT aliasKeyTBS_len aliasKeyCRT_len aliasKeyCRT))

(* Get Functions *)

assume 
val spec_x509_get_deviceIDCSR
  (deviceIDCRI_len: U32.t)
  (deviceIDCRI_buf: Seq.seq U8.t)
  (deviceIDCRI_sig: Seq.seq U8.t)
  : deviceIDCSR_t deviceIDCRI_len

assume 
val x509_get_deviceIDCSR
  (deviceIDCRI_len: U32.t)
  (deviceIDCRI_buf: A.array U8.t)
  (deviceIDCRI_sig: A.array U8.t)
  (#buf_perm #sig_perm:perm)
  (#buf #sig:Ghost.erased (Seq.seq U8.t))
  : stt (deviceIDCSR_t deviceIDCRI_len)
    (A.pts_to deviceIDCRI_buf buf_perm buf `star`
     A.pts_to deviceIDCRI_sig sig_perm sig)
     (fun res -> 
        A.pts_to deviceIDCRI_buf buf_perm buf `star`
        A.pts_to deviceIDCRI_sig sig_perm sig `star`
        pure (res == spec_x509_get_deviceIDCSR deviceIDCRI_len buf sig))

assume 
val spec_x509_get_deviceIDCRI
  (version: x509_version_t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  (ku: U32.t)
  (deviceID_pub: Seq.seq U8.t)
  : deviceIDCRI_t

assume 
val x509_get_deviceIDCRI
  (version: x509_version_t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  (ku: U32.t)
  (deviceID_pub: A.array U8.t)
  (#pub_perm:perm)
  (#deviceID_pub0: Ghost.erased (Seq.seq U8.t))
  : stt deviceIDCRI_t
    (A.pts_to deviceID_pub pub_perm deviceID_pub0)
    (fun res -> 
      A.pts_to deviceID_pub pub_perm deviceID_pub0 `star`
      pure (res == spec_x509_get_deviceIDCRI version s_common s_org s_country ku deviceID_pub0))

assume 
val spec_x509_get_aliasKeyTBS
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (fwid deviceID_pub aliasKey_pub:Seq.seq U8.t)
  : aliasKeyTBS_t

assume
val x509_get_aliasKeyTBS
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (fwid:A.larray U8.t 32)
  (deviceID_pub:A.larray U8.t 32)
  (aliasKey_pub:A.larray U8.t 32)
  (#fwid_perm #deviceID_perm #aliasKey_perm:perm)
  (#fwid0 #deviceID0 #aliasKey0:Ghost.erased (Seq.seq U8.t))
  : stt aliasKeyTBS_t
  (A.pts_to fwid fwid_perm fwid0 `star`
   A.pts_to deviceID_pub deviceID_perm deviceID0 `star`
   A.pts_to aliasKey_pub aliasKey_perm aliasKey0)
  (fun res ->
    A.pts_to fwid fwid_perm fwid0 `star`
    A.pts_to deviceID_pub deviceID_perm deviceID0 `star`
    A.pts_to aliasKey_pub aliasKey_perm aliasKey0 `star`
    pure (res == spec_x509_get_aliasKeyTBS aliasKeyCRT_ingredients fwid0 deviceID0 aliasKey0))
  
assume 
val spec_x509_get_aliasKeyCRT
  (aliasKeyTBS_len: U32.t)
  (aliasKeyTBS_buf: Seq.seq U8.t)
  (aliasKeyTBS_sig: Seq.seq U8.t)
  : aliasKeyCRT_t aliasKeyTBS_len

assume 
val x509_get_aliasKeyCRT
  (aliasKeyTBS_len: U32.t)
  (aliasKeyTBS_buf: A.array U8.t)
  (aliasKeyTBS_sig: A.array U8.t)
  (#buf_perm #sig_perm:perm)
  (#buf #sig:Ghost.erased (Seq.seq U8.t))
  : stt (aliasKeyCRT_t aliasKeyTBS_len)
    (A.pts_to aliasKeyTBS_buf buf_perm buf `star`
     A.pts_to aliasKeyTBS_sig sig_perm sig)
     (fun res -> 
        A.pts_to aliasKeyTBS_buf buf_perm buf `star`
        A.pts_to aliasKeyTBS_sig sig_perm sig `star`
        pure (res == spec_x509_get_aliasKeyCRT aliasKeyTBS_len buf sig))