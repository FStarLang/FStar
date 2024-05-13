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
module M = Pulse.Lib.MutexToken
module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module HT = Pulse.Lib.HashTable
module PHT = Pulse.Lib.HashTable.Spec

open PulseCore.Preorder
open Pulse.Lib.OnRange
open Pulse.Lib.HashTable.Type
open Pulse.Lib.HashTable
open Pulse.Lib.MutexToken

assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a

assume val sid_hash : sid_t -> SZ.t

[@@ Rust_const_fn]
```pulse
fn initialize_global_state ()
  requires emp
  returns b:(r:gref & mutex (dpe_inv r))
  ensures emp
{
  let r = ghost_alloc #_ #pcm all_sids_unused;
  with _v. rewrite (ghost_pcm_pts_to r (G.reveal (G.hide _v))) as
                   (ghost_pcm_pts_to r _v);
  fold (dpe_inv r None);
  let m = new_mutex (dpe_inv r) None;
  ((| r, m |) <: (r:gref & mutex (dpe_inv r)))
}
```

let gst : (r:gref & mutex (dpe_inv r)) = run_stt (initialize_global_state ())

let trace_ref = dfst gst

//
// DPE API implementation
//

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
fn __open_session (s:st)
  requires dpe_inv trace_ref (Some s)
  returns b:(st & option sid_t)
  ensures dpe_inv trace_ref (Some (fst b)) **
          open_session_client_perm (snd b)
{
  unfold (dpe_inv trace_ref (Some s));

  let ctr = s.st_ctr;
  let tbl = s.st_tbl;

  rewrite each
    s.st_ctr as ctr,
    s.st_tbl as tbl;

  with pht. assert (models tbl pht);
  assert (on_range (session_perm trace_ref pht) 0 (U32.v ctr));
  assert (ghost_pcm_pts_to trace_ref (sids_above_unused ctr));

  let copt = ctr `safe_add` 1ul;

  match copt {
    None -> {
      let s = { st_ctr = ctr; st_tbl = tbl };
      let ret = s, None #sid_t;
      rewrite each
        ctr as (fst ret).st_ctr,
        tbl as (fst ret).st_tbl;
      fold (dpe_inv trace_ref (Some (fst ret)));
      rewrite emp as (open_session_client_perm (snd ret));
      ret
    }

    Some ctr1 -> {
      let ret = HT.insert_if_not_full tbl ctr SessionStart;
      let tbl1 = fst ret;
      let b = snd ret;
      rewrite each fst ret as tbl1;
      with pht1. assert (models tbl1 pht1);
      if b {
        share_ trace_ref (sids_above_unused ctr)
                         (sids_above_unused ctr1)
                         (singleton ctr 1.0R emp_trace);
        share_ trace_ref (singleton ctr 1.0R emp_trace)
                         (singleton ctr 0.5R emp_trace)
                         (singleton ctr 0.5R emp_trace);
        fold (sid_pts_to trace_ref ctr emp_trace);
        fold (sid_pts_to trace_ref ctr emp_trace);
        emp_to_start_valid ();
        upd_sid_pts_to trace_ref ctr #emp_trace #emp_trace G_SessionStart;
        rewrite emp as (session_state_related SessionStart G_SessionStart);
        fold (session_state_perm trace_ref pht1 ctr);
        rewrite (session_state_perm trace_ref pht1 ctr) as
                (session_perm trace_ref pht1 (U32.v ctr));
        frame_session_perm_on_range trace_ref pht pht1 0 (U32.v ctr);
        on_range_snoc () #(session_perm trace_ref pht1) #0 #(U32.v ctr);
        let s = { st_ctr = ctr1; st_tbl = tbl1 };
        let ret = s, Some ctr;
        rewrite each
          ctr1 as (fst ret).st_ctr,
          tbl1 as (fst ret).st_tbl;
        fold (dpe_inv trace_ref (Some (fst ret)));
        fold (open_session_client_perm (Some ctr));
        ret
      } else {
        let s = { st_ctr = ctr; st_tbl = tbl1 };
        let ret = s, None #sid_t;
        rewrite each
          tbl1 as (fst ret).st_tbl,
          pht1 as pht,
          ctr as (fst ret).st_ctr;
        fold (dpe_inv trace_ref (Some (fst ret)));
        rewrite emp as (open_session_client_perm (snd ret));
        ret
      }
    }
  }
}
```
#pop-options

```pulse
fn maybe_mk_session_tbl (sopt:option st)
  requires dpe_inv trace_ref sopt
  returns s:st
  ensures dpe_inv trace_ref (Some s)
{
  match sopt {
    None -> {
      let tbl = HT.alloc #sid_t #session_state sid_hash 256sz;
      let s = {
        st_ctr = 0ul;
        st_tbl = tbl;
      };

      rewrite each tbl as s.st_tbl;

      unfold dpe_inv;
      assert (pure (Map.equal all_sids_unused (sids_above_unused s.st_ctr)));
      rewrite (ghost_pcm_pts_to trace_ref all_sids_unused) as
              (ghost_pcm_pts_to trace_ref (sids_above_unused s.st_ctr));

      with pht. assert (models s.st_tbl pht);
      on_range_empty (session_perm trace_ref pht) 0;
      rewrite (on_range (session_perm trace_ref pht) 0 0) as
              (on_range (session_perm trace_ref pht) 0 (U32.v s.st_ctr));
  
      fold (dpe_inv trace_ref (Some s));
      s
    }
    Some s -> {
      s
    }
  }
}
```

```pulse
ghost
fn to_dpe_inv_trace_ref (#s:option st) ()
  requires dpe_inv (Mkdtuple2?._1 gst) s
  ensures dpe_inv trace_ref s
{
  rewrite (dpe_inv (Mkdtuple2?._1 gst) s) as
          (dpe_inv trace_ref s)
}
```

```pulse
ghost
fn from_dpe_inv_trace_ref (#s:option st) ()
  requires dpe_inv trace_ref s
  ensures dpe_inv (Mkdtuple2?._1 gst) s
{
  rewrite (dpe_inv trace_ref s) as
          (dpe_inv (Mkdtuple2?._1 gst) s)
}
```

```pulse
fn open_session ()
  requires emp
  returns r:(option sid_t)
  ensures open_session_client_perm r
{
  let mg = M.lock (dsnd gst);
  to_dpe_inv_trace_ref ();

  let sopt = M.replace #(option st) mg None;

  let s = maybe_mk_session_tbl sopt;
  let ret = __open_session s;
  let s = fst ret;
  let sid_opt = snd ret;
  rewrite each
    fst ret as s,
    snd ret as sid_opt;
  mg := Some s;

  from_dpe_inv_trace_ref ();
  M.unlock (dsnd gst) mg;
  
  sid_opt
}
```

```pulse
ghost
fn gather_sid_pts_to (sid:sid_t) (#t0 #t1:trace)
  requires sid_pts_to trace_ref sid t0 **
           sid_pts_to trace_ref sid t1
  ensures ghost_pcm_pts_to trace_ref (singleton sid 1.0R t0) **
          pure (t0 == t1)
{
  unfold sid_pts_to;
  unfold sid_pts_to;
  gather_ trace_ref (singleton sid 0.5R t0) (singleton sid 0.5R t1);
  with v. assert (ghost_pcm_pts_to trace_ref v);
  assert (pure (Map.equal v (singleton sid 1.0R t0)));
  rewrite (ghost_pcm_pts_to trace_ref v) as
          (ghost_pcm_pts_to trace_ref (singleton sid 1.0R t0))
}
```

```pulse
ghost
fn share_sid_pts_to (sid:sid_t) (#t:trace)
  requires ghost_pcm_pts_to trace_ref (singleton sid 1.0R t)
  ensures sid_pts_to trace_ref sid t **
          sid_pts_to trace_ref sid t
{
  share_ trace_ref (singleton sid 1.0R t)
                   (singleton sid 0.5R t)
                   (singleton sid 0.5R t);
  fold sid_pts_to;
  fold sid_pts_to
}
```

```pulse
ghost
fn upd_singleton
  (sid:sid_t)
  (#t:trace)
  (s:g_session_state { valid_transition t s })
  requires ghost_pcm_pts_to trace_ref (singleton sid 1.0R t)
  ensures ghost_pcm_pts_to trace_ref (singleton sid 1.0R (next_trace t s))
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

  ghost_write trace_ref
    (singleton sid 1.0R t)
    (singleton sid 1.0R (next_trace t s))
    fp;
}
```

#push-options "--fuel 0 --ifuel 2 --split_queries no --z3rlimit_factor 2"
```pulse
fn replace_session
  (sid:sid_t)
  (t:G.erased trace)
  (sst:session_state)
  (gsst:g_session_state { valid_transition t gsst})

  requires sid_pts_to trace_ref sid t **
           session_state_related sst gsst

  returns r:session_state

  ensures session_state_related r (current_state t) **
          sid_pts_to trace_ref sid (next_trace t gsst)
{
  let mg = M.lock (dsnd gst);
  to_dpe_inv_trace_ref ();

  let sopt = M.replace mg None;
  match sopt {
    None -> {
      unfold (dpe_inv trace_ref None);
      unfold sid_pts_to;
      gather_ trace_ref all_sids_unused (singleton sid 0.5R t);
      unreachable ()
    }
    Some s -> {
      unfold (dpe_inv trace_ref (Some s));
      let ctr = s.st_ctr;
      let tbl = s.st_tbl;
      rewrite each
        s.st_ctr as ctr,
        s.st_tbl as tbl;
      with pht0. assert (models tbl pht0);
      assert (on_range (session_perm trace_ref pht0) 0 (U32.v ctr));
      if U32.lt sid ctr {
        on_range_get (U32.v sid) #(session_perm trace_ref pht0) #0 #(U32.v ctr);
        rewrite (session_perm trace_ref pht0 (U32.v sid)) as
                (session_state_perm trace_ref pht0 sid);
        unfold session_state_perm;
        gather_sid_pts_to sid;
        with t1. assert (ghost_pcm_pts_to trace_ref (singleton sid 1.0R t1));
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
              upd_singleton sid #t1 gsst;
              share_sid_pts_to sid;
              rewrite (session_state_related sst gsst) as
                      (session_state_related sst (current_state (next_trace t1 gsst)));
              fold (session_state_perm trace_ref pht sid);
              rewrite (session_state_perm trace_ref pht sid) as
                      (session_perm trace_ref pht (U32.v sid));
              frame_session_perm_on_range trace_ref pht0 pht 0 (U32.v sid);
              frame_session_perm_on_range trace_ref pht0 pht (U32.v sid + 1) (U32.v ctr);
              on_range_put 0 (U32.v sid) (U32.v ctr) #(session_perm trace_ref pht);
              let s = { st_ctr = ctr; st_tbl = tbl };
              rewrite each
                ctr as s.st_ctr,
                tbl as s.st_tbl;
              fold (dpe_inv trace_ref (Some s));
              mg := Some s;

              from_dpe_inv_trace_ref ();
              M.unlock (dsnd gst) mg;
              
              st
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
        gather_ trace_ref (sids_above_unused ctr) (singleton sid 0.5R t);
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
fn initialize_context (sid:sid_t) 
  (t:G.erased trace { trace_valid_for_initialize_context t })
  (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  (uds:A.larray U8.t (SZ.v uds_len)) 
                       
  requires A.pts_to uds #p uds_bytes **
           sid_pts_to trace_ref sid t

  returns r:ctxt_hndl_t

  ensures A.pts_to uds #p uds_bytes **
          initialize_context_client_perm sid uds_bytes
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let s = replace_session sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to trace_ref sid t1);

  match s {
    SessionStart -> {
      rewrite (session_state_related s (current_state t)) as emp;
      let context = init_engine_ctxt uds;
      let handle = prng ();
      let s = Available { handle; context };
      rewrite (context_perm context (Engine_context_repr uds_bytes)) as
              (session_state_related s (G_Available (Engine_context_repr uds_bytes)));
      let s = replace_session sid t1 s (G_Available (Engine_context_repr uds_bytes));
      intro_session_state_tag_related s (current_state t1);
      with _x _y. rewrite (session_state_related _x _y) as emp;
      fold (initialize_context_client_perm sid uds_bytes);
      handle
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
fn derive_child (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
  (t:G.erased trace)
  (record:record_t)
  (#rrepr:erased repr_t { trace_and_record_valid_for_derive_child t rrepr })
  (#p:perm)
  requires record_perm record p rrepr **
           sid_pts_to trace_ref sid t
  returns b:(record_t & option ctxt_hndl_t)
  ensures record_perm (fst b) p rrepr **
          derive_child_client_perm sid t rrepr (snd b)
{
  intro_record_and_repr_tag_related record p rrepr;

  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let s = replace_session sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to trace_ref sid t1);

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
              let s = replace_session sid t1 s (G_Available nrepr);
              intro_session_state_tag_related s (current_state t1);
              let ret = (record, Some handle);
              rewrite each
                record as fst ret;
              fold (derive_child_client_perm sid t rrepr (Some handle));
              with _x _y. rewrite (session_state_related _x _y) as emp;
              ret
            }
            None -> {
              let s = SessionError;
              rewrite emp as (session_state_related s (G_SessionError (current_state t1)));
              let s = replace_session sid t1 s (G_SessionError (current_state t1));
              intro_session_state_tag_related s (current_state t1);
              let ret = (record, None #ctxt_hndl_t);
              rewrite each
                record as fst ret;
              rewrite (maybe_context_perm repr rrepr nctxt) as emp;
              fold (derive_child_client_perm sid t rrepr None);
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
fn close_session (sid:sid_t)
  (t:G.erased trace { trace_valid_for_close t })
  requires sid_pts_to trace_ref sid t
  ensures session_closed_client_perm sid t
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let s = replace_session sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to trace_ref sid t1);

  intro_session_state_tag_related s (current_state t);

  destroy_session_state s t;

  rewrite emp as (session_state_related SessionClosed (G_SessionClosed (current_state t1)));
  let s = replace_session sid t1 SessionClosed (G_SessionClosed (current_state t1));
  intro_session_state_tag_related s (current_state t1);
  with _x _y. rewrite (session_state_related _x _y) as emp;
  fold (session_closed_client_perm sid t)
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
