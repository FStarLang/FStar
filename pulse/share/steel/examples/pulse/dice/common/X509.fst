module X509
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open HACL
open L0Types
open L0Crypto

assume
val valid_deviceIDCSR_ingredients (len: US.t) : prop

assume
val valid_aliasKeyCRT_ingredients (len: US.t) : prop

assume
val length_of_deviceIDCSR (len: US.t) : US.t 

assume
val length_of_aliasKeyCRT (len: US.t) : US.t 

assume
val len_of_deviceIDCRI
  (version: x509_version_t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  : v:US.t{0 < US.v v /\ valid_deviceIDCSR_ingredients v}

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
  : v:US.t{0 < US.v v /\ valid_aliasKeyCRT_ingredients v}

(* Serialize Functions *)

assume
val spec_serialize_deviceIDCRI
  (deviceIDCRI: deviceIDCRI_t)
  (deviceIDCRI_len: US.t)
  : elseq U8.t deviceIDCRI_len

assume
val serialize_deviceIDCRI
  (deviceIDCRI: deviceIDCRI_t)
  (deviceIDCRI_len: US.t)
  (deviceIDCRI_buf: A.larray U8.t (US.v deviceIDCRI_len))
  (#deviceIDCRI_buf0: erased (elseq U8.t deviceIDCRI_len))
  : stt unit
    (A.pts_to deviceIDCRI_buf deviceIDCRI_buf0)
    (fun _ -> A.pts_to deviceIDCRI_buf (spec_serialize_deviceIDCRI 
                                                    deviceIDCRI 
                                                    deviceIDCRI_len))

assume
val spec_serialize_deviceIDCSR 
  (deviceIDCRI_len: US.t)
  (deviceIDCSR_len: US.t)
  (deviceIDCSR: deviceIDCSR_t deviceIDCRI_len)
  : elseq U8.t deviceIDCSR_len

assume
val serialize_deviceIDCSR 
  (deviceIDCRI_len: US.t)
  (deviceIDCSR: deviceIDCSR_t deviceIDCRI_len)
  (deviceIDCSR_len: US.t)
  (deviceIDCSR_buf: A.larray U8.t (US.v deviceIDCSR_len))
  (#_buf:erased (elseq U8.t deviceIDCSR_len))
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
  : elseq U8.t aliasKeyTBS_len

assume
val serialize_aliasKeyTBS
  (aliasKeyTBS: aliasKeyTBS_t)
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: A.larray U8.t (US.v aliasKeyTBS_len))
  (#aliasKeyTBS_buf0: erased (elseq U8.t aliasKeyTBS_len))
  : stt unit
    (A.pts_to aliasKeyTBS_buf aliasKeyTBS_buf0)
    (fun _ -> A.pts_to aliasKeyTBS_buf (spec_serialize_aliasKeyTBS 
                                                   aliasKeyTBS 
                                                   aliasKeyTBS_len))

assume
val spec_serialize_aliasKeyCRT
  (aliasKeyTBS_len: US.t)
  (aliasKeyCRT_len: US.t)
  (aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len)
  : elseq U8.t aliasKeyCRT_len

assume  
val serialize_aliasKeyCRT
  (aliasKeyTBS_len: US.t)
  (aliasKeyCRT: aliasKeyCRT_t aliasKeyTBS_len)
  (aliasKeyCRT_len: US.t)
  (aliasKeyCRT_buf: A.larray U8.t (US.v aliasKeyCRT_len))
  (#_buf:erased (elseq U8.t aliasKeyCRT_len))
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
  (deviceIDCRI_buf: elseq U8.t deviceIDCRI_len)
  (deviceIDCRI_sig: Seq.seq U8.t)
  : deviceIDCSR_t deviceIDCRI_len

assume 
val x509_get_deviceIDCSR
  (deviceIDCRI_len: US.t)
  (deviceIDCRI_buf: A.larray U8.t (US.v deviceIDCRI_len))
  (deviceIDCRI_sig: A.array U8.t)
  (#buf_perm #sig_perm:perm)
  (#buf:erased (elseq U8.t deviceIDCRI_len)) (#sig:erased (Seq.seq U8.t))
  : stt (deviceIDCSR_t deviceIDCRI_len)
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
  (deviceID_pub: elseq U8.t v32us)
  : deviceIDCRI_t

assume 
val x509_get_deviceIDCRI
  (version: x509_version_t)
  (s_common: string)
  (s_org: string)
  (s_country: string)
  (ku: U32.t)
  (deviceID_pub: A.larray U8.t (US.v v32us))
  (#pub_perm:perm)
  (#deviceID_pub0: erased (elseq U8.t v32us))
  : stt deviceIDCRI_t
    (A.pts_to deviceID_pub #pub_perm deviceID_pub0)
    (fun res -> 
      A.pts_to deviceID_pub #pub_perm deviceID_pub0 **
      pure (res == spec_x509_get_deviceIDCRI 
                    version s_common 
                    s_org s_country 
                    ku deviceID_pub0))

assume 
val spec_x509_get_aliasKeyTBS
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (fwid:Seq.seq U8.t)
  (deviceID_pub aliasKey_pub:elseq U8.t v32us)
  : aliasKeyTBS_t

assume
val x509_get_aliasKeyTBS
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (fwid:A.larray U8.t 32)
  (deviceID_pub:A.larray U8.t (US.v v32us))
  (aliasKey_pub:A.larray U8.t (US.v v32us))
  (#fwid_perm #deviceID_perm #aliasKey_perm:perm)
  (#fwid0:erased (Seq.seq U8.t))
  (#deviceID0 #aliasKey0:erased (elseq U8.t v32us))
  : stt aliasKeyTBS_t
  (A.pts_to fwid #fwid_perm fwid0 **
   A.pts_to deviceID_pub #deviceID_perm deviceID0 **
   A.pts_to aliasKey_pub #aliasKey_perm aliasKey0)
  (fun res ->
    A.pts_to fwid #fwid_perm fwid0 **
    A.pts_to deviceID_pub #deviceID_perm deviceID0 **
    A.pts_to aliasKey_pub #aliasKey_perm aliasKey0 **
    pure (res == spec_x509_get_aliasKeyTBS 
                  aliasKeyCRT_ingredients 
                  fwid0 deviceID0 aliasKey0))
  
assume 
val spec_x509_get_aliasKeyCRT
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: elseq U8.t aliasKeyTBS_len)
  (aliasKeyTBS_sig: Seq.seq U8.t)
  : aliasKeyCRT_t aliasKeyTBS_len

assume 
val x509_get_aliasKeyCRT
  (aliasKeyTBS_len: US.t)
  (aliasKeyTBS_buf: A.larray U8.t (US.v aliasKeyTBS_len))
  (aliasKeyTBS_sig: A.array U8.t)
  (#buf_perm #sig_perm:perm)
  (#buf:erased (elseq U8.t aliasKeyTBS_len)) (#sig:erased (Seq.seq U8.t))
  : stt (aliasKeyCRT_t aliasKeyTBS_len)
    (A.pts_to aliasKeyTBS_buf #buf_perm buf **
     A.pts_to aliasKeyTBS_sig #sig_perm sig)
     (fun res -> 
        A.pts_to aliasKeyTBS_buf #buf_perm buf **
        A.pts_to aliasKeyTBS_sig #sig_perm sig **
        pure (res == spec_x509_get_aliasKeyCRT 
                      aliasKeyTBS_len 
                      buf sig))