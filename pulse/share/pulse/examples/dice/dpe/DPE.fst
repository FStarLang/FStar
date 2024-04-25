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
open HACL
open X509
open EngineTypes
open EngineCore
open L0Types
open L0Core

module G = FStar.Ghost
module PCM = FStar.PCM
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module PP = PulseCore.Preorder
module PM = Pulse.Lib.PCMMap
module FP = Pulse.Lib.PCM.FractionalPreorder
module M = Pulse.Lib.Mutex
module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module HT = Pulse.Lib.HashTable
module PHT = Pulse.Lib.HashTable.Spec

open PulseCore.Preorder
open Pulse.Lib.OnRange
open Pulse.Lib.HashTable.Type
open Pulse.Lib.HashTable
open Pulse.Lib.Mutex

assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a

//
// Concrete state setup
//

type ctxt_hndl_t = U32.t

type sid_t : eqtype = U32.t

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
  | G_Available r0, G_Available r1 -> next_repr r0 r1

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
  if UInt.fits sid 32
  then session_state_perm r pht (U32.uint_to_t sid)
  else emp

noextract
let map_literal (f:sid_t -> trace_pcm_t) : pcm_t = Map.map_literal f

noextract
let all_sids_unused : pcm_t = map_literal (fun _ -> Some 1.0R, emp_trace)

let sids_above_unused (s:sid_t) : GTot pcm_t = map_literal (fun sid ->
  if U32.lt sid s then None, emp_trace
  else Some 1.0R, emp_trace)

//
// Main invariant
//
let inv (r:gref) (s:option st) : vprop =
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
                  on_range (session_perm r pht) 0 (U32.v s.st_ctr))

let inv_is_small (r:gref) (s:option st)
  : Lemma (is_small (inv r s))
          [SMTPat (is_small (inv r s))] = ()


//
// The DPE API
//

let open_session_client_perm (r:gref) (s:option sid_t) : vprop =
  match s with
  | None -> emp
  | Some s ->
    exists* t. sid_pts_to r s t ** pure (current_state t == G_SessionStart)

val open_session (r:gref) (m:mutex (option st))
  : stt (mutex (option st) & option sid_t)
        (requires mutex_live m (inv r))
        (ensures fun b ->
           mutex_live (fst b) (inv r) **
           open_session_client_perm r (snd b) **
           pure (fst b == m))

noextract
let trace_valid_for_initialize_context (t:trace) : prop =
  current_state t == G_SessionStart

let initialize_context_client_perm (r:gref) (sid:sid_t) (uds:Seq.seq U8.t) =
  exists* t. sid_pts_to r sid t **
             pure (current_state t == G_Available (Engine_context_repr uds))

val initialize_context (r:gref) (m:mutex (option st))
  (sid:sid_t) 
  (t:G.erased trace { trace_valid_for_initialize_context t })
  (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  (uds:A.larray U8.t (SZ.v uds_len)) 
  : stt (mutex (option st) & ctxt_hndl_t)
        (requires
           mutex_live m (inv r) **
           A.pts_to uds #p uds_bytes **
           sid_pts_to r sid t)
        (ensures fun b ->
           mutex_live (fst b) (inv r) **
           A.pts_to uds #p uds_bytes **
           initialize_context_client_perm r sid uds_bytes)

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

let derive_child_client_perm (r:gref) (sid:sid_t) (t0:trace) (repr:repr_t) (c:option ctxt_hndl_t)
  : vprop =
  match c with
  | None ->
    exists* t1. sid_pts_to r sid t1 **
                pure (current_state t1 == G_SessionError (G_InUse (current_state t0)))
  | Some _ ->
    exists* t1. sid_pts_to r sid t1 **
                pure (derive_child_post_trace repr t1)

val derive_child (r:gref) (m:mutex (option st)) (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
  (t:G.erased trace)
  (record:record_t)
  (#rrepr:erased repr_t { trace_and_record_valid_for_derive_child t rrepr })
  (#p:perm)
  : stt (mutex (option st) & record_t & option ctxt_hndl_t)
        (requires
           mutex_live m (inv r) **
           record_perm record p rrepr **
           sid_pts_to r sid t)
        (ensures fun b ->
           mutex_live (tfst b) (inv r) **
           record_perm (tsnd b) p rrepr **
           derive_child_client_perm r sid t rrepr (tthd b))


noextract
let trace_valid_for_close (t:trace) : prop =
  match current_state t with
  | G_UnInitialized
  | G_SessionClosed _
  | G_InUse _ -> False
  | _ -> True

let session_closed_client_perm (r:gref) (sid:sid_t) (t0:trace) =
  exists* t1. sid_pts_to r sid t1 **
              pure (current_state t1 == G_SessionClosed (G_InUse (current_state t0)))

val close_session
  (r:gref)
  (m:mutex (option st))
  (sid:sid_t)
  (t:G.erased trace { trace_valid_for_close t })
  : stt (mutex (option st))
        (requires
           mutex_live m (inv r) **
           sid_pts_to r sid t)
        (ensures fun m ->
           mutex_live m (inv r) **
           session_closed_client_perm r sid t)

assume val sid_hash : sid_t -> SZ.t

[@@ Rust_const_fn]
```pulse
fn initialize_global_state ()
  requires emp
  returns b:(gref & mutex (option st))
  ensures mutex_live (snd b) (inv (fst b))
{
  let r = ghost_alloc #_ #pcm all_sids_unused;
  with _v. rewrite (ghost_pcm_pts_to r (G.reveal (G.hide _v))) as
                   (ghost_pcm_pts_to r _v);
  fold (inv r None);
  let m = new_mutex (inv r) None;
  let s = ((r, m) <: gref & mutex (option st));
  rewrite each
    r as fst s,
    m as snd s;
  s
}
```

let global_state : gref & mutex (option st) = run_stt (initialize_global_state ())

//
// DPE API implementation
//

```pulse
ghost
fn intro_context_and_repr_tag_related (c:context_t) (r:context_repr_t)
  requires context_perm c r
  ensures context_perm c r ** pure (context_and_repr_tag_related c r)
{
  let b = context_and_repr_tag_related c r;
  if b {
    ()
  } else {
    rewrite (context_perm c r) as (pure False);
    unreachable ()
  }
}
```

```pulse
ghost
fn rewrite_context_perm_engine (c:context_t) (ec:engine_context_t) (#r:context_repr_t)
  requires context_perm c r **
           pure (c == Engine_context ec)
  returns uds:Ghost.erased (Seq.seq U8.t)
  ensures engine_context_perm ec uds ** pure (r == Engine_context_repr uds)
{
  match r {
    Engine_context_repr uds -> {
      rewrite (context_perm c r) as
              (engine_context_perm ec uds);
      hide uds
    }
    _ -> {
      assume_ (pure (~ (Engine_context_repr? r)));
      rewrite (context_perm c r) as
              (pure False);
      unreachable ()

    }
  }
}
```

```pulse
ghost
fn rewrite_context_perm_l0 (c:context_t) (lc:l0_context_t) (#r:context_repr_t)
  requires context_perm c r **
           pure (c == L0_context lc)
  returns lrepr:Ghost.erased l0_context_repr_t
  ensures l0_context_perm lc lrepr ** pure (r == L0_context_repr lrepr)
{
  match r {
    L0_context_repr lrepr -> {
      rewrite (context_perm c r) as
              (l0_context_perm lc lrepr);
      hide lrepr
    }
    _ -> {
      assume_ (pure (~ (L0_context_repr? r)));
      rewrite (context_perm c r) as
              (pure False);
      unreachable ()
    }
  }
}
```

```pulse
ghost
fn rewrite_context_perm_l1 (c:context_t) (lc:l1_context_t) (#r:context_repr_t)
  requires context_perm c r **
           pure (c == L1_context lc)
  returns lrepr:Ghost.erased l1_context_repr_t
  ensures l1_context_perm lc lrepr ** pure (r == L1_context_repr lrepr)
{
  match r {
    L1_context_repr lrepr -> {
      rewrite (context_perm c r) as
              (l1_context_perm lc lrepr);
      hide lrepr
    }
    _ -> {
      assume_ (pure (~ (L1_context_repr? r)));
      rewrite (context_perm c r) as
              (pure False);
      unreachable ()
    }
  }
}
```

```pulse
ghost
fn intro_record_and_repr_tag_related (r:record_t) (p:perm) (repr:repr_t)
  requires record_perm r p repr
  ensures record_perm r p repr **
          pure (record_perm_and_repr_tag_related r repr)
{
  let b = record_perm_and_repr_tag_related r repr;
  if b {
    ()
  } else {
    rewrite (record_perm r p repr) as (pure False);
    unreachable ()
  }
}
```

```pulse
ghost
fn rewrite_record_perm_engine (r:record_t) (er:engine_record_t) (#p:perm) (#repr:repr_t)
  requires record_perm r p repr **
           pure (r == Engine_record er)
  returns erepr:Ghost.erased engine_record_repr
  ensures engine_record_perm er p erepr ** pure (repr == Engine_repr erepr)
{
  match repr {
    Engine_repr erepr -> {
      rewrite (record_perm r p repr)
          as  (engine_record_perm er p erepr);
      hide erepr
    }
    L0_repr _ -> {
      rewrite (record_perm r p repr)
          as  (pure False);
      unreachable ()
    }
  }
}
```

```pulse
ghost
fn rewrite_record_perm_l0 (r:record_t) (lr:l0_record_t) (#p:perm) (#repr:repr_t)
  requires record_perm r p repr **
           pure (r == L0_record lr)
  returns r0:Ghost.erased l0_record_repr_t
  ensures l0_record_perm lr p r0 ** pure (repr == L0_repr r0)
{
  match repr {
    Engine_repr _ -> {
      rewrite (record_perm r p repr)
          as  (pure False);
      unreachable ()
    }
    L0_repr r0 -> {
      rewrite (record_perm r p repr)
          as  (l0_record_perm lr p r0);
      hide r0
    }
  }
}
```

//
// A wrapper over ghost_gather
//
// ghost_gather takes erased arguments,
//   sometimes that leads to unnecessary reveals and hides
//
// This version works much better
//
```pulse
ghost
fn gather_ (r:gref)
  (v0 v1:pcm_t)
  requires ghost_pcm_pts_to r v0 **
           ghost_pcm_pts_to r v1
  returns _:squash (PCM.composable pcm v0 v1)
  ensures ghost_pcm_pts_to r (PCM.op pcm v0 v1)
{
  ghost_gather r v0 v1;
  with _v. rewrite (ghost_pcm_pts_to r _v) as
                   (ghost_pcm_pts_to r (PCM.op pcm v0 v1))
}
```

//
// A gather to work with map pcm
//
// The caller provides v and the proof that
//   v is `Map.equal` to op of v0 and v1
//
// 
```pulse
ghost
fn gather_v (r:gref)
  (v0 v1 v:pcm_t)
  requires ghost_pcm_pts_to r v0 **
           ghost_pcm_pts_to r v1 **
           pure (PCM.composable pcm v0 v1 ==> Map.equal (PCM.op pcm v0 v1) v)
  ensures ghost_pcm_pts_to r v **
          pure (PCM.composable pcm v0 v1)
{
  ghost_gather r v0 v1;
  with _v. rewrite (ghost_pcm_pts_to r _v) as
                   (ghost_pcm_pts_to r v)
}
```

//
// Corresponding share, with a Map.equal proof in the precondition
//
```pulse
ghost
fn share_ (r:gref)
  (v v0 v1:pcm_t)
  requires ghost_pcm_pts_to r v **
           pure (PCM.composable pcm v0 v1 /\
                 Map.equal (PCM.op pcm v0 v1) v)
  ensures ghost_pcm_pts_to r v0 **
          ghost_pcm_pts_to r v1
{
  rewrite (ghost_pcm_pts_to r v) as
          (ghost_pcm_pts_to r (PCM.op pcm v0 v1));
  ghost_share r v0 v1;
}
```

noextract
let full (t0:trace) = Some #perm 1.0R, t0

noextract
let half (t0:trace) = Some #perm 0.5R, t0

```pulse
ghost
fn upd_sid_pts_to
  (r:gref) (sid:sid_t)
  (#t0 #t1:trace)
  (s:g_session_state { valid_transition t0 s })

  requires sid_pts_to r sid t0 **
           sid_pts_to r sid t1
  ensures sid_pts_to r sid (next_trace t0 s) **
          sid_pts_to r sid (next_trace t0 s) **
          pure (t0 == t1)
{
  unfold sid_pts_to;
  unfold sid_pts_to;

  gather_v r (singleton sid 0.5R t0)
             (singleton sid 0.5R t1)
             (singleton sid 1.0R t0);

  let fp : PCM.frame_preserving_upd trace_pcm (full t0) (full (next_trace t0 s)) =
    mk_frame_preserving_upd t0 s;

  assert (pure (Map.equal (Map.upd (singleton sid 1.0R t0) sid (full (next_trace t0 s)))
                          (singleton sid 1.0R (next_trace t0 s))));

  let fp : PCM.frame_preserving_upd pcm (singleton sid 1.0R t0) (singleton sid 1.0R (next_trace t0 s)) =
    PM.lift_frame_preserving_upd #_ #_ #trace_pcm
      (full t0)
      (full (next_trace t0 s))
      fp
      (singleton sid 1.0R t0) sid;

  ghost_write r
    (singleton sid 1.0R t0)
    (singleton sid 1.0R (next_trace t0 s))
    fp;

  share_ r (singleton sid 1.0R (next_trace t0 s))
           (singleton sid 0.5R (next_trace t0 s))
           (singleton sid 0.5R (next_trace t0 s));

  fold (sid_pts_to r sid (next_trace t0 s));
  fold (sid_pts_to r sid (next_trace t0 s));
}
```

assume val safe_add (i j:U32.t)
  : o:option U32.t { Some? o ==> U32.v (Some?.v o) == U32.v i + U32.v j }

noextract
let session_table_eq_on_range
  (pht0 pht1:pht_t)
  (i j:nat)
  : prop =
  forall (k:sid_t). i <= U32.v k && U32.v k < j ==> PHT.lookup pht0 k == PHT.lookup pht1 k

```pulse
ghost
fn frame_session_perm_at_sid
  (r:gref)
  (pht0 pht1:pht_t)
  (i j:nat)
  (_:squash (session_table_eq_on_range pht0 pht1 i j))
  (sid:(sid:nat { i <= sid /\ sid < j }))
  requires session_perm r pht0 sid
  ensures session_perm r pht1 sid
{
  if (UInt.fits sid 32) {
    let sid32 = U32.uint_to_t sid;
    rewrite (session_perm r pht0 sid) as
            (session_state_perm r pht0 sid32);
    unfold session_state_perm;
    fold (session_state_perm r pht1 sid32);
    rewrite (session_state_perm r pht1 sid32) as
            (session_perm r pht1 sid)
  } else {
    rewrite (session_perm r pht0 sid) as
            (session_perm r pht1 sid)
  }
}
```

```pulse
ghost
fn frame_session_perm_on_range
  (r:gref)
  (pht0 pht1:pht_t)
  (i j:nat)
  requires on_range (session_perm r pht0) i j **
           pure (session_table_eq_on_range pht0 pht1 i j)
  ensures on_range (session_perm r pht1) i j
{
  Pulse.Lib.OnRange.on_range_weaken
    (session_perm r pht0)
    (session_perm r pht1)
    i j
    (frame_session_perm_at_sid r pht0 pht1 i j ())
}
```

let emp_to_start_valid () : Lemma (valid_transition emp_trace G_SessionStart) = ()

#push-options "--fuel 0 --ifuel 2 --split_queries no --z3rlimit_factor 2"
```pulse
fn __open_session (r:gref) (s:st)
  requires inv r (Some s)
  returns b:(st & option sid_t)
  ensures inv r (Some (fst b)) **
          open_session_client_perm r (snd b)
{
  unfold (inv r (Some s));

  let ctr = s.st_ctr;
  let tbl = s.st_tbl;

  rewrite each
    s.st_ctr as ctr,
    s.st_tbl as tbl;

  with pht. assert (models tbl pht);
  assert (on_range (session_perm r pht) 0 (U32.v ctr));
  assert (ghost_pcm_pts_to r (sids_above_unused ctr));

  let copt = ctr `safe_add` 1ul;

  match copt {
    None -> {
      let s = { st_ctr = ctr; st_tbl = tbl };
      let ret = s, None #sid_t;
      rewrite each
        ctr as (fst ret).st_ctr,
        tbl as (fst ret).st_tbl;
      fold (inv r (Some (fst ret)));
      rewrite emp as (open_session_client_perm r (snd ret));
      ret
    }

    Some ctr1 -> {
      let ret = HT.insert_if_not_full tbl ctr SessionStart;
      let tbl1 = fst ret;
      let b = snd ret;
      rewrite each fst ret as tbl1;
      with pht1. assert (models tbl1 pht1);
      if b {
        share_ r (sids_above_unused ctr)
                 (sids_above_unused ctr1)
                 (singleton ctr 1.0R emp_trace);
        share_ r (singleton ctr 1.0R emp_trace)
                 (singleton ctr 0.5R emp_trace)
                 (singleton ctr 0.5R emp_trace);
        fold (sid_pts_to r ctr emp_trace);
        fold (sid_pts_to r ctr emp_trace);
        emp_to_start_valid ();
        upd_sid_pts_to r ctr #emp_trace #emp_trace G_SessionStart;
        rewrite emp as (session_state_related SessionStart G_SessionStart);
        fold (session_state_perm r pht1 ctr);
        rewrite (session_state_perm r pht1 ctr) as
                (session_perm r pht1 (U32.v ctr));
        frame_session_perm_on_range r pht pht1 0 (U32.v ctr);
        on_range_snoc () #(session_perm r pht1) #0 #(U32.v ctr);
        let s = { st_ctr = ctr1; st_tbl = tbl1 };
        let ret = s, Some ctr;
        rewrite each
          ctr1 as (fst ret).st_ctr,
          tbl1 as (fst ret).st_tbl;
        fold (inv r (Some (fst ret)));
        fold (open_session_client_perm r (Some ctr));
        ret
      } else {
        let s = { st_ctr = ctr; st_tbl = tbl1 };
        let ret = s, None #sid_t;
        rewrite each
          tbl1 as (fst ret).st_tbl,
          pht1 as pht,
          ctr as (fst ret).st_ctr;
        fold (inv r (Some (fst ret)));
        rewrite emp as (open_session_client_perm r (snd ret));
        ret
      }
    }
  }
}
```
#pop-options

```pulse
fn maybe_mk_session_tbl (r:gref) (sopt:option st)
  requires inv r sopt
  returns s:st
  ensures inv r (Some s)
{
  match sopt {
    None -> {
      let tbl = HT.alloc #sid_t #session_state sid_hash 256sz;
      let s = {
        st_ctr = 0ul;
        st_tbl = tbl;
      };

      rewrite each tbl as s.st_tbl;

      unfold inv;
      assert (pure (Map.equal all_sids_unused (sids_above_unused s.st_ctr)));
      rewrite (ghost_pcm_pts_to r all_sids_unused) as
              (ghost_pcm_pts_to r (sids_above_unused s.st_ctr));

      with pht. assert (models s.st_tbl pht);
      on_range_empty (session_perm r pht) 0;
      rewrite (on_range (session_perm r pht) 0 0) as
              (on_range (session_perm r pht) 0 (U32.v s.st_ctr));
  
      fold (inv r (Some s));
      s
    }
    Some s -> {
      s
    }
  }
}
```

```pulse
fn open_session (r:gref) (m:mutex (option st))
  requires mutex_live m (inv r)
  returns b:(mutex (option st) & option sid_t)
  ensures mutex_live (fst b) (inv r) **
          open_session_client_perm r (snd b) **
          pure (fst b == m)
{
  let mg = lock m;
  let sopt = M.replace mg None;

  let s = maybe_mk_session_tbl r sopt;
  let ret = __open_session r s;
  let s = fst ret;
  let sid_opt = snd ret;
  rewrite each
    fst ret as s,
    snd ret as sid_opt;
  mg := Some s;
  unlock m mg;

  let ret = (m, sid_opt);

  rewrite each
    m as fst ret,
    sid_opt as snd ret;
  ret
}
```

```pulse
ghost
fn gather_sid_pts_to (r:gref) (sid:sid_t) (#t0 #t1:trace)
  requires sid_pts_to r sid t0 **
           sid_pts_to r sid t1
  ensures ghost_pcm_pts_to r (singleton sid 1.0R t0) **
          pure (t0 == t1)
{
  unfold sid_pts_to;
  unfold sid_pts_to;
  gather_ r (singleton sid 0.5R t0) (singleton sid 0.5R t1);
  with v. assert (ghost_pcm_pts_to r v);
  assert (pure (Map.equal v (singleton sid 1.0R t0)));
  rewrite (ghost_pcm_pts_to r v) as
          (ghost_pcm_pts_to r (singleton sid 1.0R t0))
}
```

```pulse
ghost
fn share_sid_pts_to (r:gref) (sid:sid_t) (#t:trace)
  requires ghost_pcm_pts_to r (singleton sid 1.0R t)
  ensures sid_pts_to r sid t **
          sid_pts_to r sid t
{
  share_ r (singleton sid 1.0R t)
           (singleton sid 0.5R t)
           (singleton sid 0.5R t);
  fold sid_pts_to;
  fold sid_pts_to
}
```

```pulse
ghost
fn upd_singleton
  (r:gref) (sid:sid_t)
  (#t:trace)
  (s:g_session_state { valid_transition t s })
  requires ghost_pcm_pts_to r (singleton sid 1.0R t)
  ensures ghost_pcm_pts_to r (singleton sid 1.0R (next_trace t s))
{
  let fp : PCM.frame_preserving_upd trace_pcm (full t) (full (next_trace t s)) =
    mk_frame_preserving_upd t s;

  assert (pure (Map.equal (Map.upd (singleton sid 1.0R t) sid (full (next_trace t s)))
                          (singleton sid 1.0R (next_trace t s))));

  let fp : PCM.frame_preserving_upd pcm (singleton sid 1.0R t) (singleton sid 1.0R (next_trace t s)) =
    PM.lift_frame_preserving_upd #_ #_ #trace_pcm
      (full t)
      (full (next_trace t s))
      fp
      (singleton sid 1.0R t) sid;

  ghost_write r
    (singleton sid 1.0R t)
    (singleton sid 1.0R (next_trace t s))
    fp;
}
```

#push-options "--fuel 0 --ifuel 2 --split_queries no --z3rlimit_factor 2"
```pulse
fn replace_session
  (r:gref)
  (m:mutex (option st))
  (sid:sid_t)
  (t:G.erased trace)
  (sst:session_state)
  (gsst:g_session_state { valid_transition t gsst})

  requires mutex_live m (inv r) **
           sid_pts_to r sid t **
           session_state_related sst gsst

  returns b:(mutex (option st) & session_state)

  ensures mutex_live (fst b) (inv r) **
          session_state_related (snd b) (current_state t) **
          sid_pts_to r sid (next_trace t gsst)
{
  let mg = lock m;
  let sopt = M.replace mg None;
  match sopt {
    None -> {
      unfold (inv r None);
      unfold sid_pts_to;
      gather_ r all_sids_unused (singleton sid 0.5R t);
      unreachable ()
    }
    Some s -> {
      unfold (inv r (Some s));
      let ctr = s.st_ctr;
      let tbl = s.st_tbl;
      rewrite each
        s.st_ctr as ctr,
        s.st_tbl as tbl;
      with pht0. assert (models tbl pht0);
      assert (on_range (session_perm r pht0) 0 (U32.v ctr));
      if U32.lt sid ctr {
        on_range_get (U32.v sid) #(session_perm r pht0) #0 #(U32.v ctr);
        rewrite (session_perm r pht0 (U32.v sid)) as (session_state_perm r pht0 sid);
        unfold session_state_perm;
        gather_sid_pts_to r sid;
        with t1. assert (ghost_pcm_pts_to r (singleton sid 1.0R t1));
        assert (pure (t1 == t));
        let ret = HT.lookup tbl sid;
        let tbl = tfst ret;
        let b = tsnd ret;
        let idx = tthd ret;
        rewrite each
          tfst ret as tbl,
          tsnd ret as b,
          tthd ret as idx;
        with pht. assert (models tbl pht);
        if b {
          match idx {
            Some idx -> {
              let ret = HT.replace #_ #_ #pht tbl idx sid sst ();
              let tbl = fst ret;
              let st = snd ret;
              rewrite each
                fst ret as tbl,
                snd ret as st;
              with _s. rewrite (session_state_related _s (current_state t1)) as
                               (session_state_related st (current_state t1));
              with pht. assert (models tbl pht);
              upd_singleton r sid #t1 gsst;
              share_sid_pts_to r sid;
              rewrite (session_state_related sst gsst) as
                      (session_state_related sst (current_state (next_trace t1 gsst)));
              fold (session_state_perm r pht sid);
              rewrite (session_state_perm r pht sid) as
                      (session_perm r pht (U32.v sid));
              frame_session_perm_on_range r pht0 pht 0 (U32.v sid);
              frame_session_perm_on_range r pht0 pht (U32.v sid + 1) (U32.v ctr);
              on_range_put 0 (U32.v sid) (U32.v ctr) #(session_perm r pht);
              let s = { st_ctr = ctr; st_tbl = tbl };
              rewrite each
                ctr as s.st_ctr,
                tbl as s.st_tbl;
              fold (inv r (Some s));
              mg := Some s;
              unlock m mg;
              let ret = (m, st);
              rewrite each
                m as fst ret,
                st as snd ret;
              ret
            }
            None -> {
              unreachable ()
            }
          }
        } else {
          //
          // AR: TODO: would be nice if we can prove this can't happen
          //           i.e. if sid is in pht, then its lookup should succeed
          assume_ (pure False);
          unreachable ()
        }
      } else {
        unfold sid_pts_to;
        gather_ r (sids_above_unused ctr) (singleton sid 0.5R t);
        unreachable ()
      }
    }
  }
}
```
#pop-options

```pulse
fn init_engine_ctxt
  (uds:A.array U8.t { A.length uds == SZ.v uds_len })
  (#p:perm)
  (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  requires A.pts_to uds #p uds_bytes
  returns ctxt:context_t
  ensures A.pts_to uds #p uds_bytes **
          context_perm ctxt (Engine_context_repr uds_bytes)
{ 
  let uds_buf = V.alloc 0uy uds_len;
  A.pts_to_len uds;
  V.pts_to_len uds_buf;

  V.to_array_pts_to uds_buf;
  A.memcpy uds_len uds (V.vec_to_array uds_buf);
  V.to_vec_pts_to uds_buf;

  let engine_context = mk_engine_context_t uds_buf;

  rewrite each uds_buf as (engine_context.uds);
  fold (engine_context_perm engine_context uds_bytes);

  let ctxt = mk_context_t_engine engine_context;
  rewrite (engine_context_perm engine_context uds_bytes) 
       as (context_perm ctxt (Engine_context_repr uds_bytes));
  ctxt
}
```

assume val prng () : stt ctxt_hndl_t emp (fun _ -> emp)

let session_state_tag_related (s:session_state) (gs:g_session_state) : GTot bool =
  match s, gs with
  | SessionStart, G_SessionStart
  | InUse, G_InUse _
  | SessionClosed, G_SessionClosed _
  | SessionError, G_SessionError _
  | Available _, G_Available _ -> true
  | _ -> false


```pulse
ghost
fn intro_session_state_tag_related (s:session_state) (gs:g_session_state)
  requires session_state_related s gs
  ensures session_state_related s gs **
          pure (session_state_tag_related s gs)
{
  let b = session_state_tag_related s gs;
  if b {
    ()
  } else {
    rewrite (session_state_related s gs) as
            (pure False);
    unreachable ()
  }
}
```

#push-options "--fuel 2 --ifuel 2 --split_queries no"
```pulse
fn initialize_context (r:gref) (m:mutex (option st))
  (sid:sid_t) 
  (t:G.erased trace { trace_valid_for_initialize_context t })
  (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  (uds:A.larray U8.t (SZ.v uds_len)) 
                       
  requires mutex_live m (inv r) **
           A.pts_to uds #p uds_bytes **
           sid_pts_to r sid t

  returns b:(mutex (option st) & ctxt_hndl_t)

  ensures mutex_live (fst b) (inv r) **
          A.pts_to uds #p uds_bytes **
          initialize_context_client_perm r sid uds_bytes
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let ret = replace_session r m sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to r sid t1);

  let m = fst ret;
  let s = snd ret;

  rewrite each
    fst ret as m,
    snd ret as s;
  
  match s {
    SessionStart -> {
      rewrite (session_state_related s (current_state t)) as emp;
      let context = init_engine_ctxt uds;
      let handle = prng ();
      let s = Available { handle; context };
      rewrite (context_perm context (Engine_context_repr uds_bytes)) as
              (session_state_related s (G_Available (Engine_context_repr uds_bytes)));
      let ret = replace_session r m sid t1 s (G_Available (Engine_context_repr uds_bytes));
      intro_session_state_tag_related (snd ret) (current_state t1);
      with _x _y. rewrite (session_state_related _x _y) as emp;
      let m = fst ret;
      rewrite each
        fst ret as m,
        snd ret as InUse;
      let ret = (m, handle);
      rewrite each
        m as fst ret,
        handle as snd ret;
      fold (initialize_context_client_perm r sid uds_bytes);
      ret
    }
    InUse -> {
      rewrite (session_state_related s (current_state t)) as
              (pure False);
      unreachable ()
    }
    SessionClosed -> {
      rewrite (session_state_related s (current_state t)) as
              (pure False);
      unreachable ()
    }
    SessionError -> {
      rewrite (session_state_related s (current_state t)) as
              (pure False);
      unreachable ()
    }
    Available _ -> {
      rewrite (session_state_related s (current_state t)) as
              (pure False);
      unreachable ()
    }
  }
}
```
#pop-options

```pulse
fn init_l0_ctxt
  (cdi:A.array U8.t { A.length cdi == SZ.v dice_digest_len })
  (#engine_repr:erased engine_record_repr)
  (#s:erased (Seq.seq U8.t))
  (#uds_bytes:erased (Seq.seq U8.t))
  (_:squash (cdi_functional_correctness s uds_bytes engine_repr /\
             l0_is_authentic engine_repr))
  requires A.pts_to cdi s
  returns ctxt:l0_context_t
  ensures
    A.pts_to cdi s **
    l0_context_perm ctxt (mk_l0_context_repr_t uds_bytes s engine_repr)
{
  let cdi_buf = V.alloc 0uy dice_digest_len;
  A.pts_to_len cdi;
  V.pts_to_len cdi_buf;

  V.to_array_pts_to cdi_buf;
  A.memcpy dice_digest_len cdi (V.vec_to_array cdi_buf);
  V.to_vec_pts_to cdi_buf;
  
  let l0_context = mk_l0_context_t cdi_buf;
  let l0_context_repr = hide (mk_l0_context_repr_t uds_bytes s engine_repr);
  rewrite each cdi_buf as (l0_context.cdi);
  fold (l0_context_perm l0_context l0_context_repr);
  l0_context
}
```

```pulse
fn init_l1_ctxt (deviceIDCSR_len: SZ.t) (aliasKeyCRT_len: SZ.t) 
                (deviceID_priv: A.larray U8.t (SZ.v v32us)) (deviceID_pub: A.larray U8.t (SZ.v v32us))
                (aliasKey_priv: A.larray U8.t (SZ.v v32us)) (aliasKey_pub: A.larray U8.t (SZ.v v32us)) 
                (deviceIDCSR: A.larray U8.t (SZ.v deviceIDCSR_len)) (aliasKeyCRT: A.larray U8.t (SZ.v aliasKeyCRT_len))
                (deviceID_label_len aliasKey_label_len: erased hkdf_lbl_len)
                (cdi:erased (Seq.seq U8.t))
                (repr:erased l0_record_repr_t)
                (deviceIDCSR_ingredients:erased deviceIDCSR_ingredients_t)
                (aliasKeyCRT_ingredients:erased aliasKeyCRT_ingredients_t)
                (#deviceID_priv0 #deviceID_pub0 #aliasKey_priv0 #aliasKey_pub0
                 #deviceIDCSR0 #aliasKeyCRT0:erased (Seq.seq U8.t))
                (_:squash (
                   valid_hkdf_ikm_len dice_digest_len /\
                   aliasKey_functional_correctness
                     dice_hash_alg dice_digest_len cdi repr.fwid
                     aliasKey_label_len repr.aliasKey_label 
                     aliasKey_pub0 aliasKey_priv0 /\
                   deviceIDCSR_functional_correctness
                     dice_hash_alg dice_digest_len cdi
                     deviceID_label_len repr.deviceID_label deviceIDCSR_ingredients 
                     deviceIDCSR_len deviceIDCSR0 /\
                   aliasKeyCRT_functional_correctness
                     dice_hash_alg dice_digest_len cdi repr.fwid
                     deviceID_label_len repr.deviceID_label aliasKeyCRT_ingredients 
                     aliasKeyCRT_len aliasKeyCRT0 aliasKey_pub0))
              
  requires A.pts_to deviceID_priv deviceID_priv0 ** 
           A.pts_to deviceID_pub deviceID_pub0 ** 
           A.pts_to aliasKey_priv aliasKey_priv0 ** 
           A.pts_to aliasKey_pub aliasKey_pub0 ** 
           A.pts_to deviceIDCSR deviceIDCSR0 **
           A.pts_to aliasKeyCRT aliasKeyCRT0
  returns ctxt:l1_context_t
  ensures 
    A.pts_to deviceID_priv deviceID_priv0 ** 
    A.pts_to deviceID_pub deviceID_pub0 **
    A.pts_to aliasKey_priv aliasKey_priv0 ** 
    A.pts_to aliasKey_pub aliasKey_pub0 ** 
    A.pts_to deviceIDCSR deviceIDCSR0 **
    A.pts_to aliasKeyCRT aliasKeyCRT0 **
    l1_context_perm ctxt (mk_l1_context_repr_t 
                            deviceID_label_len aliasKey_label_len deviceID_priv0 deviceID_pub0
                            aliasKey_priv0 aliasKey_pub0 aliasKeyCRT_len aliasKeyCRT0 deviceIDCSR_len
                            deviceIDCSR0 cdi repr deviceIDCSR_ingredients aliasKeyCRT_ingredients)
{
  let deviceID_pub_buf = V.alloc 0uy v32us;
  let deviceID_priv_buf = V.alloc 0uy v32us;
  let aliasKey_priv_buf = V.alloc 0uy v32us;
  let aliasKey_pub_buf = V.alloc 0uy v32us;
  let deviceIDCSR_buf = V.alloc 0uy deviceIDCSR_len;
  let aliasKeyCRT_buf = V.alloc 0uy aliasKeyCRT_len;

  V.to_array_pts_to deviceID_pub_buf;
  V.to_array_pts_to deviceID_priv_buf;
  V.to_array_pts_to aliasKey_priv_buf;
  V.to_array_pts_to aliasKey_pub_buf;
  V.to_array_pts_to deviceIDCSR_buf;
  V.to_array_pts_to aliasKeyCRT_buf;
  memcpy v32us deviceID_priv (V.vec_to_array deviceID_priv_buf);
  memcpy v32us deviceID_pub (V.vec_to_array deviceID_pub_buf);
  memcpy v32us aliasKey_priv (V.vec_to_array aliasKey_priv_buf);
  memcpy v32us aliasKey_pub (V.vec_to_array aliasKey_pub_buf);
  memcpy deviceIDCSR_len deviceIDCSR (V.vec_to_array deviceIDCSR_buf);
  memcpy aliasKeyCRT_len aliasKeyCRT (V.vec_to_array aliasKeyCRT_buf);
  V.to_vec_pts_to deviceID_pub_buf;
  V.to_vec_pts_to deviceID_priv_buf;
  V.to_vec_pts_to aliasKey_priv_buf;
  V.to_vec_pts_to aliasKey_pub_buf;
  V.to_vec_pts_to deviceIDCSR_buf;
  V.to_vec_pts_to aliasKeyCRT_buf;

  let l1_context = mk_l1_context_t 
    deviceID_priv_buf deviceID_pub_buf aliasKey_priv_buf aliasKey_pub_buf 
    aliasKeyCRT_buf deviceIDCSR_buf;
  let l1_context_repr = hide (mk_l1_context_repr_t 
    deviceID_label_len aliasKey_label_len deviceID_priv0 deviceID_pub0
    aliasKey_priv0 aliasKey_pub0 aliasKeyCRT_len aliasKeyCRT0 deviceIDCSR_len
    deviceIDCSR0 cdi repr deviceIDCSR_ingredients aliasKeyCRT_ingredients);

  rewrite each deviceID_priv_buf  as l1_context.deviceID_priv,
          deviceID_pub_buf  as l1_context.deviceID_pub,
          aliasKey_priv_buf as l1_context.aliasKey_priv,
          aliasKey_pub_buf  as l1_context.aliasKey_pub,
          deviceIDCSR_buf   as l1_context.deviceIDCSR,
          aliasKeyCRT_buf   as l1_context.aliasKeyCRT;

  fold (l1_context_perm l1_context l1_context_repr);
  l1_context
}
```

```pulse
ghost
fn l0_record_perm_aux (r1 r2:l0_record_t) (#p:perm) (#repr:l0_record_repr_t)
  requires l0_record_perm r1 p repr **
           pure (r1.fwid == r2.fwid /\
                 r1.deviceID_label_len == r2.deviceID_label_len /\
                 r1.deviceID_label == r2.deviceID_label /\
                 r1.aliasKey_label_len == r2.aliasKey_label_len /\
                 r1.aliasKey_label == r2.aliasKey_label)
  ensures l0_record_perm r2 p repr
{
  unfold (l0_record_perm r1 p repr);
  rewrite (V.pts_to r1.fwid #p repr.fwid) as (V.pts_to r2.fwid #p repr.fwid);
  rewrite (V.pts_to r1.deviceID_label #p repr.deviceID_label)
       as (V.pts_to r2.deviceID_label #p repr.deviceID_label);
  rewrite (V.pts_to r1.aliasKey_label #p repr.aliasKey_label)
       as (V.pts_to r2.aliasKey_label #p repr.aliasKey_label);
  fold (l0_record_perm r2 p repr)
}
```

noextract
let context_derives_from_input (r:context_repr_t) (rrepr:repr_t) : prop =
  match r, rrepr with
  | L0_context_repr l0_repr, Engine_repr erepr ->
    l0_repr.repr == erepr
  | L1_context_repr l1_repr, L0_repr lrepr ->
    l1_repr.repr == lrepr
  | _ -> False    
    
let maybe_context_perm (r:context_repr_t) (rrepr:repr_t) (c:option context_t) =
  match c with
  | Some c ->
    exists* repr. context_perm c repr **
                  pure (next_repr r repr /\ context_derives_from_input repr rrepr)
  | None -> emp

noextract
let valid_context_and_record_for_derive_child (c:context_repr_t) (r:repr_t) : prop =
  match c, r with
  | Engine_context_repr _, Engine_repr _ -> True
  | L0_context_repr _, L0_repr _ -> True
  | _ -> False

```pulse
fn derive_child_from_context
    (context:context_t)
    (record:record_t)
    p
    (#record_repr: erased repr_t)
    (#context_repr:erased (context_repr_t))
    (_:squash (valid_context_and_record_for_derive_child context_repr record_repr))

  requires
    context_perm context context_repr **
    record_perm record p record_repr
  returns res:(context_t & record_t & option context_t)
  ensures
    context_perm (tfst res) context_repr **
    record_perm (tsnd res) p record_repr **
    maybe_context_perm context_repr record_repr (tthd res)
{
  intro_context_and_repr_tag_related context context_repr;
  intro_record_and_repr_tag_related record p record_repr;
 
  match context {
    Engine_context c -> {
      match record {
        Engine_record r -> {
          let uds_bytes = rewrite_context_perm_engine context c;
          unfold (engine_context_perm c uds_bytes);

          let engine_record_repr = rewrite_record_perm_engine record r;

          let mut cdi = [| 0uy; dice_digest_len |];

          V.to_array_pts_to c.uds;
          let ret = EngineCore.engine_main cdi (V.vec_to_array c.uds) r;
          V.to_vec_pts_to c.uds;

          let r = fst ret;
          rewrite each fst ret as r;

          with s. assert (A.pts_to cdi s);
          fold (engine_context_perm c uds_bytes);
          rewrite (engine_context_perm c uds_bytes)
               as (context_perm (Engine_context c) context_repr);
          rewrite (engine_record_perm r p engine_record_repr)
               as (record_perm (Engine_record r) p record_repr);

          match snd ret {
            DICE_SUCCESS -> {
              let l0_ctxt = init_l0_ctxt cdi #engine_record_repr #s #uds_bytes ();
              with l0_ctxt_repr. assert (l0_context_perm l0_ctxt l0_ctxt_repr);
              fold (context_perm (L0_context l0_ctxt) (L0_context_repr l0_ctxt_repr));
              fold (maybe_context_perm context_repr record_repr (Some (L0_context l0_ctxt)));
              let ret = (Engine_context c, Engine_record r, Some (L0_context l0_ctxt));
              rewrite each
                Engine_context c as tfst ret,
                Engine_record r as tsnd ret,
                Some (L0_context l0_ctxt) as tthd ret;
              ret
            }

            DICE_ERROR -> {
              A.zeroize dice_digest_len cdi;
              let ret = (Engine_context c, Engine_record r, None #context_t);
              rewrite emp as (maybe_context_perm context_repr record_repr (tthd ret));
              rewrite each
                Engine_context c as tfst ret,
                Engine_record r as tsnd ret;
              ret
            }
          }
        }
        L0_record _ -> {
          unreachable ()
        }
      }
    }
    
    L0_context c -> {
      match record {
        L0_record r -> {
          let cr = rewrite_context_perm_l0 context c;
          unfold (l0_context_perm c cr);
          with s. assert (V.pts_to c.cdi s);

          let r0 = rewrite_record_perm_l0 record r;

          let deviceIDCRI_len_and_ing = len_of_deviceIDCRI r.deviceIDCSR_ingredients;
          let deviceIDCSR_ingredients = fst deviceIDCRI_len_and_ing;
          let deviceIDCRI_len = snd deviceIDCRI_len_and_ing;

          let aliasKeyTBS_len_and_ing = len_of_aliasKeyTBS r.aliasKeyCRT_ingredients;
          let aliasKeyCRT_ingredients = fst aliasKeyTBS_len_and_ing;
          let aliasKeyTBS_len = snd aliasKeyTBS_len_and_ing;

          let deviceIDCSR_len = length_of_deviceIDCSR deviceIDCRI_len;
          let aliasKeyCRT_len = length_of_aliasKeyCRT aliasKeyTBS_len;

          let mut deviceID_pub = [| 0uy; v32us |];
          let mut deviceID_priv = [| 0uy; v32us |];
          let mut aliasKey_pub = [| 0uy; v32us |];
          let mut aliasKey_priv = [| 0uy; v32us |];

          let deviceIDCSR = V.alloc 0uy deviceIDCSR_len;
          let aliasKeyCRT = V.alloc 0uy aliasKeyCRT_len;

          V.to_array_pts_to deviceIDCSR;
          V.to_array_pts_to aliasKeyCRT;
          V.to_array_pts_to c.cdi;

          let r1 = {
            fwid = r.fwid;
            deviceID_label_len = r.deviceID_label_len;
            deviceID_label = r.deviceID_label;
            aliasKey_label_len = r.aliasKey_label_len;
            aliasKey_label = r.aliasKey_label;
            deviceIDCSR_ingredients;
            aliasKeyCRT_ingredients;
          } <: l0_record_t;
          l0_record_perm_aux r r1;

          let r2 = L0Core.l0_main  (V.vec_to_array c.cdi) deviceID_pub deviceID_priv 
                                   aliasKey_pub aliasKey_priv 
                                   aliasKeyTBS_len aliasKeyCRT_len (V.vec_to_array aliasKeyCRT)
                                   deviceIDCRI_len deviceIDCSR_len (V.vec_to_array deviceIDCSR) r1;

          V.to_vec_pts_to c.cdi;

          fold (l0_context_perm c cr);
          rewrite (l0_context_perm c cr)
               as (context_perm (L0_context c) context_repr);
          rewrite (l0_record_perm r2 p r0)
               as (record_perm (L0_record r2) p record_repr);


          with deviceID_priv0. assert (A.pts_to deviceID_priv deviceID_priv0);
          with deviceID_pub0. assert (A.pts_to deviceID_pub deviceID_pub0);
          with aliasKey_priv0. assert (A.pts_to aliasKey_priv aliasKey_priv0);
          with aliasKey_pub0. assert (A.pts_to aliasKey_pub aliasKey_pub0);
          with deviceIDCSR0. assert (A.pts_to (V.vec_to_array deviceIDCSR) deviceIDCSR0);
          with aliasKeyCRT0. assert (A.pts_to (V.vec_to_array aliasKeyCRT) aliasKeyCRT0);

          let l1_context = init_l1_ctxt 
                      deviceIDCSR_len aliasKeyCRT_len deviceID_priv deviceID_pub
                      aliasKey_priv aliasKey_pub (V.vec_to_array deviceIDCSR) (V.vec_to_array aliasKeyCRT)
                      (hide r2.deviceID_label_len)
                      (hide r2.aliasKey_label_len) s r0 (hide r2.deviceIDCSR_ingredients) (hide r2.aliasKeyCRT_ingredients)
                      #deviceID_priv0 #deviceID_pub0 #aliasKey_priv0 #aliasKey_pub0
                      #deviceIDCSR0 #aliasKeyCRT0
                      ();

          with l1_context_repr. assert (l1_context_perm l1_context l1_context_repr);
          fold (context_perm (L1_context l1_context) (L1_context_repr l1_context_repr));

          V.to_vec_pts_to deviceIDCSR;
          V.to_vec_pts_to aliasKeyCRT;
          V.free deviceIDCSR;
          V.free aliasKeyCRT;

          fold (maybe_context_perm context_repr record_repr (Some (L1_context l1_context)));
          let ret = (L0_context c, L0_record r2, Some (L1_context l1_context));
          rewrite each
            L0_context c as tfst ret,
            L0_record r2 as tsnd ret,
            Some (L1_context l1_context) as tthd ret;

          ret
        }
        Engine_record _ -> {
          unreachable ()
        }
      }
    }

    L1_context _ -> {
      unreachable ()
    }
  }
}
```

```pulse
ghost
fn rewrite_session_state_related_available
  handle
  context
  (s:session_state { s == Available { handle; context } })
  (t:trace)
  requires session_state_related s (current_state t)
  returns r:G.erased context_repr_t
  ensures context_perm context r ** pure (current_state t == G_Available r)
{
  let cur = current_state t;
  intro_session_state_tag_related s cur;
  let repr = G_Available?.repr cur;
  rewrite (session_state_related s cur) as
          (context_perm context repr);
  hide repr
}
```

```pulse 
fn destroy_ctxt (ctxt:context_t) (#repr:erased context_repr_t)
  requires context_perm ctxt repr
  ensures emp
{
  match ctxt
  {
    Engine_context c ->
    {
      let uds = rewrite_context_perm_engine ctxt c;
      unfold (engine_context_perm c uds);
      V.free c.uds;
    }
    L0_context c ->
    {
      let r = rewrite_context_perm_l0 ctxt c;
      unfold (l0_context_perm c r);
      V.free c.cdi;
    }
    L1_context c ->
    {
      let r = rewrite_context_perm_l1 ctxt c;
      unfold (l1_context_perm c r);
      V.free c.deviceID_priv;
      V.free c.deviceID_pub;
      V.free c.aliasKey_priv;
      V.free c.aliasKey_pub;
      V.free c.aliasKeyCRT;
      V.free c.deviceIDCSR;
    }
  }
}
```

#push-options "--fuel 2 --ifuel 2 --split_queries no"
```pulse
fn derive_child (r:gref) (m:mutex (option st)) (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
  (t:G.erased trace)
  (record:record_t)
  (#rrepr:erased repr_t { trace_and_record_valid_for_derive_child t rrepr })
  (#p:perm)
  requires mutex_live m (inv r) **
           record_perm record p rrepr **
           sid_pts_to r sid t
  returns b:(mutex (option st) & record_t & option ctxt_hndl_t)
  ensures mutex_live (tfst b) (inv r) **
          record_perm (tsnd b) p rrepr **
          derive_child_client_perm r sid t rrepr (tthd b)
{
  intro_record_and_repr_tag_related record p rrepr;

  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let ret = replace_session r m sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to r sid t1);

  let m = fst ret;
  let s = snd ret;

  rewrite each
    fst ret as m,
    snd ret as s;

  match s {
    Available hc -> {
      match hc.context {
        L1_context _ -> {
          rewrite (session_state_related s (current_state t)) as
                  (pure False);
          unreachable ()
        }
        _ -> {
          assume_ (pure (~ (L1_context? hc.context)));
          let repr = rewrite_session_state_related_available hc.handle hc.context s t;
          intro_context_and_repr_tag_related hc.context repr;
          let ret = derive_child_from_context hc.context record p #rrepr #repr ();

          let octxt = tfst ret;
          let record = tsnd ret;
          let nctxt = tthd ret;
          rewrite each
            tfst ret as octxt,
            tsnd ret as record,
            tthd ret as nctxt;
          
          destroy_ctxt octxt;
          match nctxt {
            Some nctxt -> {
              unfold (maybe_context_perm repr rrepr (Some nctxt));
              with nrepr. assert (context_perm nctxt nrepr);
              intro_context_and_repr_tag_related nctxt nrepr;
              let handle = prng ();
              let s = Available { handle; context = nctxt };
              rewrite (context_perm nctxt nrepr) as
                      (session_state_related s (G_Available nrepr));
              let ret = replace_session r m sid t1 s (G_Available nrepr);
              intro_session_state_tag_related (snd ret) (current_state t1);
              let m = fst ret;
              rewrite each
                fst ret as m,
                snd ret as InUse;
              let ret = (m, record, Some handle);
              rewrite each
                m as tfst ret,
                record as tsnd ret;
              fold (derive_child_client_perm r sid t rrepr (Some handle));
              with _x _y. rewrite (session_state_related _x _y) as emp;
              ret
            }
            None -> {
              let s = SessionError;
              rewrite emp as (session_state_related s (G_SessionError (current_state t1)));
              let ret = replace_session r m sid t1 s (G_SessionError (current_state t1));
              intro_session_state_tag_related (snd ret) (current_state t1);
              let m = fst ret;
              rewrite each
                fst ret as m,
                snd ret as InUse;
              let ret = (m, record, None #ctxt_hndl_t);
              rewrite each
                m as tfst ret,
                record as tsnd ret;
              rewrite (maybe_context_perm repr rrepr nctxt) as emp;
              fold (derive_child_client_perm r sid t rrepr None);
              with _x _y. rewrite (session_state_related _x _y) as emp;
              ret
            }
          }
        }
      }
    }
    SessionStart -> {
      rewrite (session_state_related s (current_state t)) as
              (pure False);
      unreachable ()
    }
    InUse -> {
      rewrite (session_state_related s (current_state t)) as
              (pure False);
      unreachable ()
    }
    SessionClosed -> {
      rewrite (session_state_related s (current_state t)) as
              (pure False);
      unreachable ()
    }
    SessionError -> {
      rewrite (session_state_related s (current_state t)) as
              (pure False);
      unreachable ()
    }
  }
}
```

```pulse
fn destroy_session_state (s:session_state) (t:G.erased trace)
  requires session_state_related s (current_state t)
  ensures emp
{
  intro_session_state_tag_related s (current_state t);
  match s {
    Available hc -> {
      rewrite_session_state_related_available hc.handle hc.context s t;
      destroy_ctxt hc.context
    }
    _ -> {
      assume_ (pure (~ (Available? s)));
      with _x _y. rewrite (session_state_related _x _y) as emp
    }
  }
}
```

```pulse
fn close_session (r:gref) (m:mutex (option st)) (sid:sid_t)
  (t:G.erased trace { trace_valid_for_close t })
  requires mutex_live m (inv r) **
           sid_pts_to r sid t
  returns m:mutex (option st)
  ensures mutex_live m (inv r) **
          session_closed_client_perm r sid t
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let ret = replace_session r m sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to r sid t1);

  let m = fst ret;
  let s = snd ret;
  rewrite each
    fst ret as m,
    snd ret as s;

  intro_session_state_tag_related s (current_state t);

  destroy_session_state s t;

  rewrite emp as (session_state_related SessionClosed (G_SessionClosed (current_state t1)));
  let ret = replace_session r m sid t1 SessionClosed (G_SessionClosed (current_state t1));
  intro_session_state_tag_related (snd ret) (current_state t1);
  let m = fst ret;
  rewrite each
    fst ret as m,
    snd ret as InUse;
  with _x _y. rewrite (session_state_related _x _y) as emp;
  fold (session_closed_client_perm r sid t);
  m
}
```

(*
  GetProfile: Part of DPE API 
  Get the DPE's profile. 
*)
```pulse
fn get_profile ()
  requires emp
  returns d:profile_descriptor_t
  ensures emp
{
  mk_profile_descriptor
    (*name=*)""
    (*dpe_spec_version=*)1ul
    (*max_message_size=*)0ul // irrelevant: using direct interface
    (*uses_multi_part_messages=*)false
    (*supports_concurrent_operations=*)false // irrelevant by uses_multi_part_messages
    (*supports_encrypted_sessions=*)false // irrelevant by uses_multi_part_messages
    (*supports_derived_sessions=*)false // irrelevant by supports_encrypted_sessions
    (*max_sessions=*)0sz // irrelevant by supports_encrypted_sessions
    (*session_protocol=*)"" // irrelevant by supports_encrypted_sessions
    (*supports_session_sync=*)false // by supports_encrypted_sessions
    (*session_sync_policy=*)"" // irrelevant by supports_session_sync
    (*session_migration_protocol=*)"" // irrelevant by supports_session_migration
    (*supports_default_context=*)false
    (*supports_context_handles=*)true 
    (*max_contexts_per_session=*)1sz // 1 context per session
    (*max_context_handle_size=*)16sz // 16 bits
    (*supports_auto_init=*)false // irrelevant by supports_default_context
    (*supports_simulation=*)false
    (*supports_attestation=*)false
    (*supports_sealing=*)false 
    (*supports_get_profile=*)true
    (*supports_open_session=*)false // irrelevant by supports_encrypted_sessions
    (*supports_close_session=*)false // irrelevant by supports_encrypted_sessions
    (*supports_sync_session=*)false // irrelevant by supports_encrypted_sessions
    (*supports_export_session=*)false
    (*supports_import_session=*)false
    (*supports_init_context=*)true
    (*supports_certify_key=*)false // irrelevant by supports_attestation
    (*supports_sign=*)false // irrelevant by supports_attestation
    (*supports_seal=*)false // irrelevant by supports_sealing
    (*supports_unseal=*)false // irrelevant by supports_sealing
    (*supports_sealing_public=*)false // irrelevant by supports_sealing
    (*supports_rotate_context_handle=*)true
    (*dice_derivation=*)"" // FIXME: name for DICE algorithms
    (*asymmetric_derivation=*)"" // irrelevant by supports_attestation
    (*symmetric_derivation=*)"" // irrelevant by supports_attestation
    (*supports_any_label=*)false
    (*supported_labels=*)"" // FIXME: what are lables?
    (*initial_derivation=*)"" // FIXME: name?
    (*input_format=*)"" // FIXME: create CDDL spec for input record formats
    (*supports_internal_inputs=*)false
    (*supports_internal_dpe_info=*)false // irrelevant by supports_internal_inputs
    (*supports_internal_dpe_dice=*)false // irrelevant by supports_internal_inputs
    (*internal_dpe_info_type=*)"" // irrelevant by supports_internal_inputs
    (*internal_dpe_dice_type=*)"" // irrelevant by supports_internal_inputs
    (*internal_inputs=*)"" // irrelevant by supports_internal_inputs
    (*supports_certificates=*)false // irrelevant by supports_attestation
    (*max_certificate_size=*)0sz // irrelevant by supports_certificates
    (*max_certificate_chain_size=*)0sz // irrelevant by supports_certificates
    (*appends_more_certificates=*)false // irrelevant by supports_certificates
    (*supports_certificate_policies=*)false // irrelevant by supports_certificates
    (*supports_policy_identity_init=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_identity_loc=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_attest_init=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_attest_loc=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_assert_init=*)false // irrelevant by supports_certificate_policies
    (*supports_policy_assert_loc=*)false // irrelevant by supports_certificate_policies
    (*certificate_policies=*)"" // irrelevant by supports_certificate_policies
    (*supports_eca_certificates=*)false // irrelevant by supports_certificate_policies
    (*eca_certificate_format=*)"" // irrelevant by supports_eca_certificates
    (*leaf_certificate_format=*)"" // irrelevant by supports_certificates
    (*public_key_format=*)"" // irrelevant by supports_asymmetric_unseal
    (*supports_external_key=*)false // irrelevant by supports_certificates
    (*to_be_signed_format=*)"" // irrelevant by supports_sign
    (*signature_format=*)"" // irrelevant by supports_sign
    (*supports_symmetric_sign=*)false // irrelevant by supports_attestation
    (*supports_asymmetric_unseal=*)false // irrelevant by supports_attestation
    (*supports_unseal_policy=*)false// irrelevant by supports_sealing
    (*unseal_policy_format=*)"" // irrelevant by supports_unseal_policy 
}
```
