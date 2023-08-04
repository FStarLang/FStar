module DPE
open Pulse.Lib.Pervasives
open HACL
open X509
open EngineTypes
open EngineCore
open L0Types
open L0Core
module L = Pulse.Lib.SpinLock
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open LinearScanHashTable
open Pulse.Lib.HashTable
module PHT = Pulse.Lib.HashTable
module LSHT = LinearScanHashTable

(* Engine Context *)
noeq
type engine_context = { uds: A.larray U8.t (US.v uds_len); }

val engine_context_perm (c:engine_context) : vprop

let mk_engine_context uds : engine_context = {uds}

(* L0 Context *)
noeq
type l0_context = { cdi: A.larray U8.t (US.v dice_digest_len); }

val l0_context_perm (c:l0_context) : vprop

let mk_l0_context cdi : l0_context = {cdi}

(* L1 Context *)
noeq
type l1_context = { deviceID_priv: A.larray U8.t (US.v v32us);
                    deviceID_pub: A.larray U8.t (US.v v32us);
                    aliasKey_priv: A.larray U8.t (US.v v32us);
                    aliasKey_pub: A.larray U8.t (US.v v32us);
                    aliasKeyCRT: A.array U8.t;
                    deviceIDCSR: A.array U8.t; }

val l1_context_perm (c:l1_context) : vprop

let mk_l1_context deviceID_priv deviceID_pub aliasKey_priv aliasKey_pub aliasKeyCRT deviceIDCSR 
  = { deviceID_priv; deviceID_pub; aliasKey_priv; aliasKey_pub; aliasKeyCRT; deviceIDCSR }

(* Context *)
noeq
type context_t = 
  | Engine_context : c:engine_context -> context_t
  | L0_context     : c:l0_context -> context_t
  | L1_context     : c:l1_context -> context_t

val context_perm (t:context_t) : vprop

let mk_engine_context_t engine_context = Engine_context engine_context
let mk_l0_context_t l0_context = L0_context l0_context
let mk_l1_context_t l1_context = L1_context l1_context

let locked_context_t = c:context_t & L.lock (context_perm c)


(* Record *)
noeq
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t

noeq
type repr_t = 
  | Engine_repr : r:engine_record_repr -> repr_t
  | L0_repr     : r:l0_record_repr -> repr_t

val record_perm (t_rec:record_t) (t_rep:repr_t) : vprop


type locked_ht_t (s:pht_sig_us) = ht:ht_t s & L.lock (exists_ (fun pht -> models s ht pht))
type sid_ref_t = r:R.ref nat & L.lock (exists_ (fun n -> R.pts_to r full_perm n))

val dpe_hashf : nat -> US.t
val sht_len : pos_us
val cht_len : pos_us
let cht_sig : pht_sig_us = mk_pht_sig_us nat locked_context_t dpe_hashf
let sht_sig : pht_sig_us = mk_pht_sig_us nat (locked_ht_t cht_sig) dpe_hashf 

val locked_sht : locked_ht_t sht_sig
val sid_ref : sid_ref_t

val prng (_:unit) : nat

val init_l0_ctxt (cdi:A.larray U8.t (US.v dice_digest_len)) (#s:erased (elseq U8.t dice_digest_len))
  : stt locked_context_t
    (A.pts_to cdi full_perm s ** pure (A.is_full_array cdi))
    (fun _ -> A.pts_to cdi full_perm s)

val init_l1_ctxt (deviceIDCSR_len: US.t) (aliasKeyCRT_len: US.t) 
                (deviceID_priv: A.larray U8.t (US.v v32us)) (deviceID_pub: A.larray U8.t (US.v v32us))
                (aliasKey_priv: A.larray U8.t (US.v v32us)) (aliasKey_pub: A.larray U8.t (US.v v32us)) 
                (deviceIDCSR: A.larray U8.t (US.v deviceIDCSR_len)) (aliasKeyCRT: A.larray U8.t (US.v aliasKeyCRT_len))
                (#s1 #s2 #s3 #s4: erased (elseq U8.t v32us)) 
                (#s5:erased (elseq U8.t deviceIDCSR_len))
                (#s6:erased (elseq U8.t aliasKeyCRT_len))
  : stt locked_context_t
     (A.pts_to deviceID_priv full_perm s1 ** 
      A.pts_to deviceID_pub full_perm s2 **  
      A.pts_to aliasKey_priv full_perm s3 **  
      A.pts_to aliasKey_pub full_perm s4 **  
      A.pts_to deviceIDCSR full_perm s5 ** 
      A.pts_to aliasKeyCRT full_perm s6) 
     (fun _ -> 
      A.pts_to deviceID_priv full_perm s1 **  
      A.pts_to deviceID_pub full_perm s2 ** 
      A.pts_to aliasKey_priv full_perm s3 **  
      A.pts_to aliasKey_pub full_perm s4 **  
      A.pts_to deviceIDCSR full_perm s5 ** 
      A.pts_to aliasKeyCRT full_perm s6)