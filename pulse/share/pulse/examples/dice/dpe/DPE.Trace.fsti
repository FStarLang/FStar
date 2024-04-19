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
module U32 = FStar.UInt32

let bytes = Seq.seq U8.t
let lbytes (n:nat) = b:bytes { Seq.length b == n }
let uds_t = lbytes (SZ.v uds_len)

type ctxt_hndl_t : Type0 = U32.t

noeq
type g_session_state : Type u#1 =
  | G_UnInitialized : g_session_state
  | G_SessionStart : g_session_state
  | G_Available : context_repr_t -> g_session_state
  | G_InUse : g_session_state -> g_session_state
  | G_SessionClosed : g_session_state -> g_session_state
  | G_SessionError : g_session_state -> g_session_state

let rec next (s0 s1:g_session_state) : prop =
  match s0, s1 with
  | G_UnInitialized, G_SessionStart -> True

  | G_UnInitialized, _
  | _, G_UnInitialized -> False

  | G_SessionStart, G_Available (Engine_context_repr _)
  | G_Available (Engine_context_repr _), G_Available (L0_context_repr _)
  | G_Available (L0_context_repr _), G_Available (L1_context_repr _) -> True

  | G_SessionClosed _, _
  | G_SessionError _, _ -> False

  | _, G_SessionClosed s
  | _, G_SessionError s -> s == s0

  | _, G_InUse s -> s == s0

  | G_InUse s, s1 -> next s s1

  | _ -> False

let rec well_formed_trace (l:list g_session_state) =
  match l with
  | []
  | [G_SessionStart] -> True
  | s1::s0::tl -> next s0 s1 /\ well_formed_trace (s0::tl)
  | _ -> False

type trace_elt : Type u#1 = l:list g_session_state { well_formed_trace l }

let trace_extension (t0 t1:trace_elt) : prop =
  Cons? t1 /\ t0 == List.Tot.tail t1

let trace_preorder : FStar.Preorder.preorder trace_elt =
  FStar.ReflexiveTransitiveClosure.closure trace_extension

open FStar.PCM
open FStar.Preorder
open PulseCore.Preorder
open PulseCore.FractionalPermission

type trace = hist trace_preorder

type pcm_t : Type u#1 = option perm & trace

let pcm_composable : symrel pcm_t =
  fun x0 x1 -> 
  match x0, x1 with
  | (None, t0), (None, t1) -> t0 `extends` t1 \/ t1 `extends` t0
  | (Some _, t0), (None, t1) -> t0 `extends` t1
  | (None, t0), (Some _, t1) -> t1 `extends` t0
  | (Some p0, t0), (Some p1, t1) -> t0 == t1 /\ (p0 +. p1) <=. 1.0R

let pcm_op (x:pcm_t) (y:pcm_t { pcm_composable x y }) : pcm_t =
  match x, y with
  | (None, t0), (None, t1) -> None, p_op trace_preorder t0 t1
  | (Some _, _), (None, _) -> x
  | (None, _), (Some _, _) -> y
  | (Some p0, t0), (Some p1, t1) -> Some (p0 +. p1), t0

let pcm_one : pcm_t = None, []

let pcm' : pcm' pcm_t = {
  composable = pcm_composable;
  op = pcm_op;
  one = pcm_one;
}

let lem_commutative : lem_commutative pcm' =
  fun _ _ -> ()

let lem_assoc_l : lem_assoc_l pcm' =
  fun _ _ _ -> ()

let lem_assoc_r : lem_assoc_r pcm' =
  fun _ _ _ -> ()

let rec extends_nil (l:trace) : Lemma (l `extends` []) =
  match l with
  | [] -> ()
  | _::tl -> extends_nil tl

let lem_is_unit : FStar.PCM.lem_is_unit pcm' =
  fun x ->
  match x with
  | Some _, t -> extends_nil t
  | None, t -> p_op_nil trace_preorder t

let pcm : pcm pcm_t = {
  p = pcm';
  comm = lem_commutative;
  assoc = lem_assoc_l;
  assoc_r = lem_assoc_r;
  is_unit = lem_is_unit;
  refine = (fun _ -> True);
}

let current_state (t:trace) : g_session_state =
  match t with
  | [] -> G_UnInitialized
  | hd::_ ->
    match hd with
    | [] -> G_UnInitialized
    | s::_ -> s

let valid_transition (t:trace) (s:g_session_state) : prop = next (current_state t) s

let next_trace (t:trace) (s:g_session_state { valid_transition t s }) : trace =
  match t with
  | [] -> [[s]]
  | hd::tl ->
    match hd with
    | [] -> [s]::t
    | l -> (s::l)::t

let mk_frame_preserving_upd
  (t:hist trace_preorder)
  (s:g_session_state { valid_transition t s })
  : frame_preserving_upd pcm (Some 1.0R, t) (Some 1.0R, next_trace t s) =
  fun _ -> Some 1.0R, next_trace t s

let snapshot (x:pcm_t) : pcm_t = None, snd x

let snapshot_idempotent (x:pcm_t)
  : Lemma (snapshot x == snapshot (snapshot x)) = ()

let snapshot_duplicable (x:pcm_t)
  : Lemma
      (requires True)
      (ensures x `pcm_composable` snapshot x) = ()

let full_perm_empty_history_compatible ()
  : Lemma (compatible pcm (Some 1.0R, []) (Some 1.0R, [])) =
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
