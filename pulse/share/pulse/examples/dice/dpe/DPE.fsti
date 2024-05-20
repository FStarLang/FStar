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

module DPE
open Pulse.Lib.Pervasives
open DPETypes
open EngineTypes
open EngineCore
open L0Types
open L0Core

module G = FStar.Ghost
module PCM = FStar.PCM
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module PM = Pulse.Lib.PCMMap
module FP = Pulse.Lib.PCM.FractionalPreorder
module A = Pulse.Lib.Array
module HT = Pulse.Lib.HashTable
module PHT = Pulse.Lib.HashTable.Spec

open PulseCore.Preorder
open Pulse.Lib.OnRange
open Pulse.Lib.HashTable.Type
open Pulse.Lib.HashTable

//
// Concrete state setup
//

type ctxt_hndl_t = U32.t

type sid_t : eqtype = U16.t

//
// A session may be in one of the following states
//
// InUse is never returned to the client
//
[@@ Rust_derive "Clone"]
noeq
type session_state =
  | SessionStart
  | Available { handle:ctxt_hndl_t; context:context_t }
  | InUse
  | SessionClosed
  | SessionError

type ht_t = ht_t sid_t session_state

//
// DPE state
// A counter for next sid
//   and a hashtable mapping sids to session state
//
noeq
type st = { st_ctr:sid_t; st_tbl:ht_t; }


//
// Ghost state set up
//

//
// Ghost session state
//
// Has a 1-1 correspondence with the concrete session state
//   except it has an G_UnInitialized
//
[@@ erasable]
noeq
type g_session_state : Type u#1 =
  | G_UnInitialized : g_session_state
  | G_SessionStart : g_session_state
  | G_Available : repr:context_repr_t -> g_session_state
  | G_InUse : g_session_state -> g_session_state
  | G_SessionClosed : g_session_state -> g_session_state
  | G_SessionError : g_session_state -> g_session_state

//
// A relation between context reprs that follow each other
//
// L0 repr should use the same UDS as the engine repr,
//   and L1 repr should use the same CDI as the L0 repr
//
noextract
let next_repr (r1 r2:context_repr_t) : prop =
  match r1, r2 with
  | Engine_context_repr uds, L0_context_repr l0_repr ->
    uds == l0_repr.uds
  | L0_context_repr l0_repr, L1_context_repr l1_repr ->
    l0_repr.cdi == l1_repr.cdi
  | _ -> False

//
// State machine
//
noextract
let rec next (s0 s1:g_session_state) : prop =
  match s0, s1 with
  //
  // UnInitialized may only go to SessionStart
  // No other incoming/outgoing edges to/from it
  //
  | G_UnInitialized, G_SessionStart -> True
  | G_UnInitialized, _
  | _, G_UnInitialized -> False

  //
  // SessionStart may go to Available with engine repr
  //
  | G_SessionStart, G_Available (Engine_context_repr _) -> True

  //
  // Available r0 may go to Available r1,
  //   as long as repr r1 follows repr r0
  //
  | G_Available r0, G_Available r1 ->
    next_repr r0 r1 \/
    (L1_context_repr? r0 /\ r0 == r1)

  //
  // SessionClosed is a terminal state
  //
  | G_SessionClosed _, _ -> False

  //
  // From any state we can go to InUse, SessionClosed, or SessionError
  //
  // These states capture the previous state
  //
  | _, G_InUse s -> s == s0
  | _, G_SessionClosed s
  | _, G_SessionError s -> s == s0

  //
  // From InUse s we can go to s1, as long as s can go to s1
  //
  | G_InUse s, s1 -> next s s1

  | _ -> False


//
// Defining traces
//

noextract
let rec well_formed_trace (l:list g_session_state) : prop =
  match l with
  | []
  | [G_SessionStart] -> True
  | s1::s0::tl -> next s0 s1 /\ well_formed_trace (s0::tl)
  | _ -> False

noextract
type trace_elt : Type u#1 = l:list g_session_state { well_formed_trace l }

noextract
let trace_extension (t0 t1:trace_elt) : prop =
  Cons? t1 /\ t0 == List.Tot.tail t1

noextract
let trace_preorder : FStar.Preorder.preorder trace_elt =
  FStar.ReflexiveTransitiveClosure.closure trace_extension

noextract
type trace = hist trace_preorder

noextract
type trace_pcm_t : Type u#1 = FP.pcm_carrier trace_preorder

//
// Trace PCM is fractional preorder PCM,
//   with trace preorder
//
noextract
let trace_pcm : FStar.PCM.pcm trace_pcm_t = FP.fp_pcm trace_preorder

//
// Current state of a trace
//
// We use UnInitialized as the current state of empty trace
//
noextract
let current_state (t:trace) : g_session_state =
  match t with
  | [] -> G_UnInitialized
  | hd::_ ->
    match hd with
    | [] -> G_UnInitialized
    | s::_ -> s

//
// Given a trace t, valid_transition t s means that
//   current state of t may go to s in the state machine
//
noextract
let valid_transition (t:trace) (s:g_session_state) : prop =
  next (current_state t) s

//
// The next trace after a transition
//
noextract
let next_trace (t:trace) (s:g_session_state { valid_transition t s }) : trace =
  match t with
  | [] -> [[s]]
  | hd::tl ->
    match hd with
    | [] -> [s]::t
    | l -> (s::l)::t

//
// A frame preserving update in the trace PCM,
//   given a valid transition
//
noextract
let mk_frame_preserving_upd
  (t:hist trace_preorder)
  (s:g_session_state { valid_transition t s })
  : FStar.PCM.frame_preserving_upd trace_pcm (Some 1.0R, t) (Some 1.0R, next_trace t s) =
  fun _ -> Some 1.0R, next_trace t s

//
// A snapshot of the trace PCM is the trace with no permission
//
noextract
let snapshot (x:trace_pcm_t) : trace_pcm_t = None, snd x

let snapshot_idempotent (x:trace_pcm_t)
  : Lemma (snapshot x == snapshot (snapshot x)) = ()

let snapshot_duplicable (x:trace_pcm_t)
  : Lemma
      (requires True)
      (ensures x `FStar.PCM.composable trace_pcm` snapshot x) = ()

let full_perm_empty_history_compatible ()
  : Lemma (FStar.PCM.compatible trace_pcm (Some 1.0R, []) (Some 1.0R, [])) = ()

noextract
type pcm_t : Type u#1 = PM.map sid_t trace_pcm_t

//
// The PCM for the DPE state is a map pcm with sid_t keys
//   and pointwise trace_pcm
noextract
let pcm : PCM.pcm pcm_t = PM.pointwise sid_t trace_pcm

[@@ erasable]
noextract
type gref = ghost_pcm_ref pcm

noextract
let emp_trace : trace = []

noextract
let singleton (sid:sid_t) (p:perm) (t:trace) : GTot pcm_t =
  Map.upd (Map.const (None, emp_trace)) sid (Some p, t)

//
// The main permission we provide to the client,
//   to capture the session history for a sid
//
noextract
let sid_pts_to (r:gref) (sid:sid_t) (t:trace) : vprop =
  ghost_pcm_pts_to r (singleton sid 0.5R t)

noextract
type pht_t = PHT.pht_t sid_t session_state

//
// Towards the global state invariant
//

let session_state_related (s:session_state) (gs:g_session_state) : v:vprop { is_small v } =
  match s, gs with
  | SessionStart, G_SessionStart
  | InUse, G_InUse _
  | SessionClosed, G_SessionClosed _
  | SessionError, G_SessionError _ -> emp

  | Available {context}, G_Available repr -> context_perm context repr

  | _ -> pure False

//
// Invariant for sessions that have been started
//
let session_state_perm (r:gref) (pht:pht_t) (sid:sid_t) : v:vprop { is_small v } =
  exists* (s:session_state) (t:trace).
    pure (PHT.lookup pht sid == Some s) **
    sid_pts_to r sid t **
    session_state_related s (current_state t)

//
// We have to do this UInt.fits since the OnRange is defined for nat keys,
//   if we parameterized it over a typeclass, we can directly use u32 keys
//   and this should go away
//
let session_perm (r:gref) (pht:pht_t) (sid:nat) =
  if UInt.fits sid 16
  then session_state_perm r pht (U16.uint_to_t sid)
  else emp

noextract
let map_literal (f:sid_t -> trace_pcm_t) : pcm_t = Map.map_literal f

noextract
let all_sids_unused : pcm_t = map_literal (fun _ -> Some 1.0R, emp_trace)

let sids_above_unused (s:sid_t) : GTot pcm_t = map_literal (fun sid ->
  if U16.lt sid s then None, emp_trace
  else Some 1.0R, emp_trace)

//
// Main invariant
//
let dpe_inv (r:gref) (s:option st) : vprop =
  match s with
  //
  // Global state is not initialized,
  //   all the sessions are unused
  //
  | None -> ghost_pcm_pts_to r all_sids_unused
  
  //
  // Global state has been initialized
  //
  | Some s ->
    //
    // sids above counter are unused
    //
    ghost_pcm_pts_to r (sids_above_unused s.st_ctr) **
    
    //
    // For sids below counter, we have the session state perm
    //
    (exists* pht. models s.st_tbl pht **
                  on_range (session_perm r pht) 0 (U16.v s.st_ctr))

let inv_is_small (r:gref) (s:option st)
  : Lemma (is_small (dpe_inv r s))
          [SMTPat (is_small (dpe_inv r s))] = ()

val trace_ref : gref

//
// The DPE API
//

let open_session_client_perm (s:option sid_t) : vprop =
  match s with
  | None -> emp
  | Some s ->
    exists* t. sid_pts_to trace_ref s t ** pure (current_state t == G_SessionStart)

val open_session ()
  : stt (option sid_t)
        (requires emp)
        (ensures fun r -> open_session_client_perm r)

noextract
let trace_valid_for_initialize_context (t:trace) : prop =
  current_state t == G_SessionStart

let initialize_context_client_perm (sid:sid_t) (uds:Seq.seq U8.t) =
  exists* t. sid_pts_to trace_ref sid t **
             pure (current_state t == G_Available (Engine_context_repr uds))

val initialize_context (sid:sid_t) 
  (t:G.erased trace { trace_valid_for_initialize_context t })
  (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  (uds:A.larray U8.t (SZ.v uds_len)) 
  : stt ctxt_hndl_t
        (requires
           A.pts_to uds #p uds_bytes **
           sid_pts_to trace_ref sid t)
        (ensures fun b ->
           A.pts_to uds #p uds_bytes **
           initialize_context_client_perm sid uds_bytes)

noextract
let trace_and_record_valid_for_derive_child (t:trace) (r:repr_t) : prop =
  match current_state t, r with
  | G_Available (Engine_context_repr _), Engine_repr _
  | G_Available (L0_context_repr _), L0_repr _ -> True
  | _ -> False

noextract
let derive_child_post_trace (r:repr_t) (t:trace) =
  match r, current_state t with
  | Engine_repr r, G_Available (L0_context_repr lrepr)
  | L0_repr r, G_Available (L1_context_repr lrepr) -> lrepr.repr == r
  | _ -> False

let derive_child_client_perm (sid:sid_t) (t0:trace) (repr:repr_t) (c:option ctxt_hndl_t)
  : vprop =
  match c with
  | None ->
    exists* t1. sid_pts_to trace_ref sid t1 **
                pure (current_state t1 == G_SessionError (G_InUse (current_state t0)))
  | Some _ ->
    exists* t1. sid_pts_to trace_ref sid t1 **
                pure (derive_child_post_trace repr t1)

val derive_child (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
  (t:G.erased trace)
  (record:record_t)
  (#rrepr:erased repr_t { trace_and_record_valid_for_derive_child t rrepr })
  : stt (option ctxt_hndl_t)
        (requires
           record_perm record 1.0R rrepr **
           sid_pts_to trace_ref sid t)
        (ensures fun b ->
           derive_child_client_perm sid t rrepr b)

noextract
let trace_valid_for_close (t:trace) : prop =
  match current_state t with
  | G_UnInitialized
  | G_SessionClosed _
  | G_InUse _ -> False
  | _ -> True

let session_closed_client_perm (sid:sid_t) (t0:trace) =
  exists* t1. sid_pts_to trace_ref sid t1 **
              pure (current_state t1 == G_SessionClosed (G_InUse (current_state t0)))

val close_session
  (sid:sid_t)
  (t:G.erased trace { trace_valid_for_close t })
  : stt unit
        (requires
           sid_pts_to trace_ref sid t)
        (ensures fun m ->
           session_closed_client_perm sid t)

noextract
let trace_valid_for_certify_key (t:trace) : prop =
  match current_state t with
  | G_Available (L1_context_repr _) -> True
  | _ -> False

let certify_key_client_perm (sid:sid_t) (t0:trace) : vprop =
  exists* t1. sid_pts_to trace_ref sid t1 **
              pure (current_state t1 == current_state t0)

val certify_key (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
  (pub_key:A.larray U8.t 32)
  (crt_len:U32.t)
  (crt:A.larray U8.t (U32.v crt_len))
  (t:G.erased trace { trace_valid_for_certify_key t })
  : stt bool
        (requires
           sid_pts_to trace_ref sid t **
           (exists* pub_key_repr crt_repr.
              A.pts_to pub_key pub_key_repr **
              A.pts_to crt crt_repr))
        (ensures fun _ ->
           certify_key_client_perm sid t **
           (exists* pub_key_repr crt_repr.
              A.pts_to pub_key pub_key_repr **
              A.pts_to crt crt_repr))
