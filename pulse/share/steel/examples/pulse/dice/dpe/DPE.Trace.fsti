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

module DPE.Trace
open Pulse.Lib.Pervasives
open DPETypes
open EngineTypes
open EngineCore
open HACL
module SZ = FStar.SizeT
module U8 = FStar.UInt8
let bytes = Seq.seq U8.t
let lbytes (n:nat) = b:bytes { Seq.length b == n }
let uds_t = lbytes (SZ.v uds_len)
val ctxt_hndl_t : Type0
val sid_t : eqtype
noeq
type state_t =
  | SessionStart:
      history:option state_t ->
      state_t

  | EngineInitialized:
      hndl:ctxt_hndl_t ->
      uds:bytes ->
      state_t

  | L0:
      hndl:ctxt_hndl_t ->
      uds:bytes ->
      cdi:bytes ->
      r:engine_record_repr {
        l0_is_authentic r /\
        EngineCore.cdi_functional_correctness cdi uds r
      } ->
      state_t

  | L1:
      hndl:ctxt_hndl_t ->
      r:l1_context_repr_t {
        valid_hkdf_ikm_len dice_digest_len /\
        L0Core.aliasKey_functional_correctness
                    dice_hash_alg dice_digest_len r.cdi r.repr.fwid
                    r.aliasKey_label_len r.repr.aliasKey_label 
                    r.aliasKey_pub r.aliasKey_priv  /\ 
        L0Core.deviceIDCSR_functional_correctness  
                    dice_hash_alg dice_digest_len r.cdi
                    r.deviceID_label_len r.repr.deviceID_label r.deviceIDCSR_ingredients 
                    r.deviceIDCSR_len r.deviceIDCSR  /\      
        L0Core.aliasKeyCRT_functional_correctness 
                    dice_hash_alg dice_digest_len r.cdi r.repr.fwid
                    r.deviceID_label_len r.repr.deviceID_label r.aliasKeyCRT_ingredients 
                    r.aliasKeyCRT_len r.aliasKeyCRT r.aliasKey_pub
      } ->
      state_t

  | SessionClosed:
      state_t

let next (s0 s1:state_t) =
    match s0, s1 with
    | SessionStart _, EngineInitialized _ _ -> True
    | EngineInitialized _ uds, L0 _ uds' cdi r -> uds==uds'
    | L0 _ _ cdi _, L1 _ l1_ctxt -> cdi == l1_ctxt.cdi
    (* destroy context preserving history *)
    | EngineInitialized _ _, SessionStart (Some h)
    | L0 _ _ _ _, SessionStart (Some h)
    | L1 _ _, SessionStart (Some h) -> 
      h == s0
    | _ -> False

let leads_to x y : prop = 
    squash (FStar.ReflexiveTransitiveClosure.closure next x y)

let rec well_formed_trace (l:list state_t) =
    match l with
    | [] -> True //empty trace
    | [SessionStart None] -> True //singleton trace begins with SessionStart
    | s1::s0::tl -> next s0 s1 /\ well_formed_trace (s0::tl)
    | _ -> False

let trace = l:list state_t { well_formed_trace l }

let trace_extension (t0 t1:trace)
  : prop
  = Cons? t1 /\ t0 == List.Tot.tail t1

let trace_preorder
  : FStar.Preorder.preorder trace
  = FStar.ReflexiveTransitiveClosure.closure trace_extension
module FRAP = Pulse.Lib.FractionalAnchoredPreorder
let degenerate_anchor
  : FRAP.anchor_rel trace_preorder
  = fun x y -> trace_preorder x y /\ True
let carrier = FRAP.knowledge degenerate_anchor
let trace_pcm
  : FStar.PCM.pcm carrier
  = FRAP.pcm #trace #trace_preorder #degenerate_anchor
module PM = Steel.PCMMap
let session_trace_pcm : PCM.pcm (PM.map sid_t carrier) = PM.pointwise sid_t trace_pcm
// let trace_ref = 
// let snapshot_value (t:trace) = (None, None), 
