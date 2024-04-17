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

open HACL
open DPETypes
open EngineTypes
open EngineCore

module SZ = FStar.SizeT
module U8 = FStar.UInt8

let bytes = Seq.seq U8.t
let lbytes (n:nat) = b:bytes { Seq.length b == n }
let uds_t = lbytes (SZ.v uds_len)

val ctxt_hndl_t : Type0

noeq
type state_t : Type u#1 =
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

type trace : Type u#1 = l:list state_t { well_formed_trace l }

let trace_extension (t0 t1:trace)
  : prop
  = Cons? t1 /\ t0 == List.Tot.tail t1

let trace_preorder
  : FStar.Preorder.preorder trace
  = FStar.ReflexiveTransitiveClosure.closure trace_extension

open FStar.PCM
open FStar.Preorder
open PulseCore.Preorder
open PulseCore.FractionalPermission

type pcm_carrier (#a:Type u#a) (p:preorder a) : Type u#a =
  option (perm & bool) & hist p

let pcm_composable #a (p:preorder a) : symrel (pcm_carrier p) =
  fun x0 x1 -> 
  match x0, x1 with
  | (None, t0), (None, t1) -> t0 `extends` t1 \/ t1 `extends` t0
  | (Some _, t0), (None, t1) -> t0 `extends` t1
  | (None, t0), (Some _, t1) -> t1 `extends` t0
  | (Some (p0, b0), t0), (Some (p1, b1), t1) ->
    b0 == b1 /\
    t0 == t1 /\
    sum_perm p0 p1 `lesser_equal_perm` full_perm

let pcm_op #a (p:preorder a)
  (x:pcm_carrier p)
  (y:pcm_carrier p { pcm_composable p x y })
  : pcm_carrier p =

  match x, y with
  | (None, t0), (None, t1) -> None, p_op p t0 t1
  | (Some _, _), (None, _) -> x
  | (None, _), (Some _, _) -> y
  | (Some (p0, b0), t0), (Some (p1, _), t1) -> Some (sum_perm p0 p1, b0), t0

let pcm_one (#a:Type) (p:preorder a) : pcm_carrier p = None, []

let pcm' (#a:Type) (p:preorder a) : pcm' (pcm_carrier p) = {
  composable = pcm_composable p;
  op = pcm_op p;
  one = pcm_one p;
}

let lem_commutative (#a:Type) (p:preorder a) : lem_commutative (pcm' p) =
  fun _ _ -> ()

let lem_assoc_l (#a:Type) (p:preorder a) : lem_assoc_l (pcm' p) =
  fun x y z ->
  match x, y, z with
  | (Some (_, _), _), (Some (_, _), _), (Some (_, _), _) -> ()
  | _ -> ()

let lem_assoc_r (#a:Type) (p:preorder a) : lem_assoc_r (pcm' p) =
  fun x y z ->
  match x, y, z with
  | (Some (_, _), _), (Some (_, _), _), (Some (_, _), _) -> ()
  | _ -> ()

let rec extends_nil (#a:Type) (#p:preorder a) (l:hist p)
  : Lemma (l `extends` []) =

  match l with
  | [] -> ()
  | _::tl -> extends_nil #a #p tl

let lem_is_unit (#a:Type) (p:preorder a) : FStar.PCM.lem_is_unit (pcm' p) =
  fun x ->
  match x with
  | Some _, t -> extends_nil t
  | None, t -> p_op_nil p t

let pcm (#a:Type) (p:preorder a) : pcm (pcm_carrier p) = {
  p = pcm' p;
  comm = lem_commutative p;
  assoc = lem_assoc_l p;
  assoc_r = lem_assoc_r p;
  is_unit = lem_is_unit p;
  refine = (fun _ -> True);
}

let mk_frame_preserving_upd (#a:Type) (p:preorder a)
  (t0:hist p) (x:a { qhistory p (x::t0) })
  (b0 b1:bool)
  : frame_preserving_upd (pcm p) (Some (full_perm, b0), t0) (Some (full_perm, b1), x::t0) =
  fun _ ->
  assert (forall frame. pcm_composable p frame (Some (full_perm, b0), t0) ==> fst frame == None);
  Some (full_perm, b1), x::t0

let mk_frame_preserving_upd_b (#a:Type) (p:preorder a)
  (t:hist p)
  (b0 b1:bool)
  : frame_preserving_upd (pcm p) (Some (full_perm, b0), t) (Some (full_perm, b1), t) =
  fun _ ->
  assert (forall frame. pcm_composable p frame (Some (full_perm, b0), t) ==> fst frame == None);
  Some (full_perm, b1), t

let snapshot (#a:Type) (#p:preorder a) (x:pcm_carrier p) : pcm_carrier p =
  None, snd x

let snapshot_idempotent (#a:Type) (#p:preorder a) (x:pcm_carrier p)
  : Lemma (snapshot x == snapshot (snapshot x)) = ()

let snapshot_duplicable (#a:Type) (#p:preorder a) (x:pcm_carrier p)
  : Lemma
      (requires True)
      (ensures x `pcm_composable p` snapshot x) = ()

let full_perm_empty_history_compatible (#a:Type) (p:preorder a) (b:bool)
  : Lemma (compatible (pcm p) (Some (full_perm, b), []) (Some (full_perm, b), [])) =
  ()


// module FRAP = Pulse.Lib.FractionalAnchoredPreorder
// let degenerate_anchor
//   : FRAP.anchor_rel trace_preorder
//   = fun x y -> trace_preorder x y /\ True
// let carrier = FRAP.knowledge degenerate_anchor
// let trace_pcm
//   : FStar.PCM.pcm carrier
//   = FRAP.pcm #trace #trace_preorder #degenerate_anchor
// module PM = Pulse.Lib.PCMMap
// let session_trace_pcm : PCM.pcm (PM.map sid_t carrier) = PM.pointwise sid_t trace_pcm
// let trace_ref = 
// let snapshot_value (t:trace) = (None, None), 
