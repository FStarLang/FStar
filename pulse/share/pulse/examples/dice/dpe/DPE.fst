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
#lang-pulse
open Pulse.Lib.Pervasives
open DPETypes
open HACL
open EngineTypes
open EngineCore
open L0Types
open L0Core

module G = FStar.Ghost
module PCM = FStar.PCM
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module PM = Pulse.Lib.PCM.Map
module M = Pulse.Lib.Mutex
module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module HT = Pulse.Lib.HashTable
module PHT = Pulse.Lib.HashTable.Spec
module Global = Pulse.Lib.GlobalVar

open PulseCore.Preorder
open Pulse.Lib.OnRange
open Pulse.Lib.HashTable.Type
open Pulse.Lib.HashTable
open Pulse.Lib.Mutex
open Pulse.Class.PtsTo
open Pulse.Class.Duplicable
open Pulse.Lib.Trade
// We assume this code will be executed on a machine where u32 fits the word size
assume SZ_fits_u32 : SZ.fits_u32

let sid_hash (s:sid_t) : SZ.t = SZ.uint16_to_sizet s

let gvar_p : (gref & mutex (option st)) -> slprop =
  fun x -> exists* p. mutex_live (snd x) #p (dpe_inv (fst x))

ghost
fn dup_gvar_p (x:(gref & mutex (option st)))
  requires gvar_p x
  ensures gvar_p x ** gvar_p x
{
  unfold gvar_p;
  Pulse.Lib.Mutex.share (snd x);
  fold (gvar_p x);
  fold (gvar_p x)
}

instance duplicable_gvar x : duplicable (gvar_p x) = { dup_f = fun _ -> dup_gvar_p x }

ghost
fn drop_mutex_live (#a:Type0) (m:mutex a) (#p:perm) (v:a -> slprop)
requires mutex_live m #p v
ensures emp
{
  drop_ (mutex_live m #p v);
}

[@@ Rust_const_fn]
fn initialize_global_state ()
  requires emp
  returns x:(gref & mutex (option st))
  ensures gvar_p x
{
  let r = GR.alloc #_ #pcm all_sids_unused;
  with _v. rewrite (GR.pts_to r (G.reveal (G.hide _v))) as
                   (GR.pts_to r _v);
  fold (dpe_inv r None);
  let m = new_mutex (dpe_inv r) None;
  fold (gvar_p (r, m));
  (r, m)
}

let gst : Global.gvar #(gref & mutex (option st)) gvar_p =
  Global.mk_gvar initialize_global_state

let trace_ref = fst (Global.read_gvar_ghost gst)

//
// DPE API implementation
//

//
// A wrapper over GR.gather
//
// GR.gather takes erased arguments,
//   sometimes that leads to unnecessary reveals and hides
//
// This version works much better
//

ghost
fn gather_ (r:gref)
  (v0 v1:pcm_t)
  requires GR.pts_to r v0 **
           GR.pts_to r v1
  returns _:squash (PCM.composable pcm v0 v1)
  ensures GR.pts_to r (PCM.op pcm v0 v1)
{
  GR.gather r v0 v1;
  with _v. rewrite (GR.pts_to r _v) as
                   (GR.pts_to r (PCM.op pcm v0 v1))
}


//
// A gather to work with map pcm
//
// The caller provides v and the proof that
//   v is `Map.equal` to op of v0 and v1
//
// 

ghost
fn gather_v (r:gref)
  (v0 v1 v:pcm_t)
  requires GR.pts_to r v0 **
           GR.pts_to r v1 **
           pure (PCM.composable pcm v0 v1 ==> Map.equal (PCM.op pcm v0 v1) v)
  ensures GR.pts_to r v **
          pure (PCM.composable pcm v0 v1)
{
  GR.gather r v0 v1;
  with _v. rewrite (GR.pts_to r _v) as
                   (GR.pts_to r v)
}


//
// Corresponding share, with a Map.equal proof in the precondition
//
ghost
fn share_ (r:gref)
  (v v0 v1:pcm_t)
  requires GR.pts_to r v **
           pure (PCM.composable pcm v0 v1 /\
                 Map.equal (PCM.op pcm v0 v1) v)
  ensures GR.pts_to r v0 **
          GR.pts_to r v1
{
  rewrite (GR.pts_to r v) as
          (GR.pts_to r (PCM.op pcm v0 v1));
  GR.share r v0 v1;
}


noextract
let full (t0:trace) = Some #perm 1.0R, t0

noextract
let half (t0:trace) = Some #perm 0.5R, t0


#restart-solver
#push-options "--z3rlimit_factor 2"
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
  unfold (sid_pts_to r sid t0);
  unfold (sid_pts_to r sid t1);

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

  GR.write r
    (singleton sid 1.0R t0)
    (singleton sid 1.0R (next_trace t0 s))
    fp;

  share_ r (singleton sid 1.0R (next_trace t0 s))
           (singleton sid 0.5R (next_trace t0 s))
           (singleton sid 0.5R (next_trace t0 s));

  fold (sid_pts_to r sid (next_trace t0 s));
  fold (sid_pts_to r sid (next_trace t0 s));
}
#pop-options

let safe_incr (i:U16.t)
  : r:option U16.t { Some? r ==> (U16.v (Some?.v r) == U16.v i + 1) } =

  let open FStar.UInt16 in
  if i <^ 0xffffus
  then Some (i +^ 1us)
  else None

noextract
let session_table_eq_on_range
  (pht0 pht1:pht_t)
  (i j:nat)
  : prop =
  forall (k:sid_t). i <= U16.v k && U16.v k < j ==> PHT.lookup pht0 k == PHT.lookup pht1 k


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
  if (UInt.fits sid 16) {
    let sid16 = U16.uint_to_t sid;
    rewrite (session_perm r pht0 sid) as
            (session_state_perm r pht0 sid16);
    unfold session_state_perm;
    with s. unfold pht_contains pht0 sid16 s;
    fold pht_contains pht1 sid16 s;
    fold (session_state_perm r pht1 sid16);
    rewrite (session_state_perm r pht1 sid16) as
            (session_perm r pht1 sid)
  } else {
    rewrite (session_perm r pht0 sid) as
            (session_perm r pht1 sid)
  }
}



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


let emp_to_start_valid () : Lemma (valid_transition emp_trace G_SessionStart) = ()

#push-options "--fuel 0 --ifuel 2 --split_queries no --z3rlimit_factor 6"

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
  assert (on_range (session_perm trace_ref pht) 0 (U16.v ctr));
  assert (GR.pts_to trace_ref (sids_above_unused ctr));

  let copt = safe_incr ctr;

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
        fold pht_contains pht1 ctr SessionStart;
        fold (session_state_perm trace_ref pht1 ctr);
        rewrite (session_state_perm trace_ref pht1 ctr) as
                (session_perm trace_ref pht1 (U16.v ctr));
        frame_session_perm_on_range trace_ref pht pht1 0 (U16.v ctr);
        on_range_snoc () #(session_perm trace_ref pht1) #0 #(U16.v ctr);
        let s = { st_ctr = ctr1; st_tbl = tbl1 };
        let ret = s, Some ctr;
        rewrite each
          ctr1 as (fst ret).st_ctr,
          tbl1 as (fst ret).st_tbl;
        fold (dpe_inv trace_ref (Some (fst ret)));
        fold (open_session_client_perm (Some ctr));
        rewrite each Some ctr as snd ret;
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

#pop-options


fn maybe_mk_session_tbl (sopt:option st)
  requires dpe_inv trace_ref sopt
  returns s:st
  ensures dpe_inv trace_ref (Some s)
{
  match sopt {
    None -> {
      let tbl = HT.alloc #sid_t #session_state sid_hash 256sz;
      let s = {
        st_ctr = 0us;
        st_tbl = tbl;
      };

      rewrite each tbl as s.st_tbl;

      unfold dpe_inv;
      assert (pure (Map.equal all_sids_unused (sids_above_unused s.st_ctr)));
      rewrite (GR.pts_to trace_ref all_sids_unused) as
              (GR.pts_to trace_ref (sids_above_unused s.st_ctr));

      with pht. assert (models s.st_tbl pht);
      on_range_empty (session_perm trace_ref pht) 0;
      rewrite (on_range (session_perm trace_ref pht) 0 0) as
              (on_range (session_perm trace_ref pht) 0 (U16.v s.st_ctr));
  
      fold (dpe_inv trace_ref (Some s));
      s
    }
    Some s -> {
      s
    }
  }
}

fn open_session ()
  requires emp
  returns r:(option sid_t)
  ensures open_session_client_perm r
{
  let r = Global.read_gvar gst;
  unfold (gvar_p r);
  let mg = M.lock (snd r);
  let sopt = M.replace #(option st) mg None;

  let s = maybe_mk_session_tbl sopt;
  let ret = __open_session s;
  let s = fst ret;
  let sid_opt = snd ret;
  rewrite each
    fst ret as s,
    snd ret as sid_opt;
  mg := Some s;

  M.unlock (snd r) mg;
  drop_mutex_live (snd r) _;

  sid_opt
}


[@@allow_ambiguous]
ghost
fn gather_sid_pts_to (sid:sid_t) (#t0 #t1:trace)
  requires sid_pts_to trace_ref sid t0 **
           sid_pts_to trace_ref sid t1
  ensures GR.pts_to trace_ref (singleton sid 1.0R t0) **
          pure (t0 == t1)
{
  unfold (sid_pts_to trace_ref sid t0);
  unfold (sid_pts_to trace_ref sid t1);
  gather_ trace_ref (singleton sid 0.5R t0) (singleton sid 0.5R t1);
  with v. assert (GR.pts_to trace_ref v);
  assert (pure (Map.equal v (singleton sid 1.0R t0)));
  rewrite (GR.pts_to trace_ref v) as
          (GR.pts_to trace_ref (singleton sid 1.0R t0))
}



ghost
fn share_sid_pts_to (sid:sid_t) (#t:trace)
  requires GR.pts_to trace_ref (singleton sid 1.0R t)
  ensures sid_pts_to trace_ref sid t **
          sid_pts_to trace_ref sid t
{
  share_ trace_ref (singleton sid 1.0R t)
                   (singleton sid 0.5R t)
                   (singleton sid 0.5R t);
  fold sid_pts_to;
  fold sid_pts_to
}



ghost
fn upd_singleton
  (sid:sid_t)
  (#t:trace)
  (s:g_session_state { valid_transition t s })
  requires GR.pts_to trace_ref (singleton sid 1.0R t)
  ensures GR.pts_to trace_ref (singleton sid 1.0R (next_trace t s))
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

  GR.write trace_ref
    (singleton sid 1.0R t)
    (singleton sid 1.0R (next_trace t s))
    fp;
}


#push-options "--fuel 0 --ifuel 2 --split_queries no --z3rlimit_factor 2"

fn replace_session
  (sid:sid_t)
  (t:G.erased trace)
  (sst:session_state)
  (gsst:g_session_state)
  requires sid_pts_to trace_ref sid t **
           session_state_related sst gsst **
           pure (valid_transition t gsst)

  returns r:session_state

  ensures
    exists* tr.
      session_state_related r (current_state t) **
      sid_pts_to trace_ref sid tr **
      pure(valid_transition t gsst /\ tr == next_trace t gsst)
{
  let r = Global.read_gvar gst;
  unfold (gvar_p r);
  rewrite each fst r as trace_ref;
  let mg = M.lock (snd r);

  let sopt = M.replace mg None;
  match sopt {
    None -> {
      unfold (dpe_inv trace_ref None);
      unfold sid_pts_to trace_ref;
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
      assert (on_range (session_perm trace_ref pht0) 0 (U16.v ctr));
      if U16.lt sid ctr {
        on_range_get (U16.v sid) #(session_perm trace_ref pht0) #0 #(U16.v ctr);
        rewrite (session_perm trace_ref pht0 (U16.v sid)) as
                (session_state_perm trace_ref pht0 sid);
        unfold session_state_perm;
        gather_sid_pts_to sid;
        with t1. assert (GR.pts_to trace_ref (singleton sid 1.0R t1));
        assert (pure (t1 == t));
        let ret = HT.lookup tbl sid;
        let tbl = fst ret;
        let idx = snd ret;
        rewrite each
          fst ret as tbl,
          snd ret as idx;
        with pht. assert (models tbl pht);
        match idx {
          Some idx -> {
            let tbl, st = HT.replace #_ #_ #pht0 tbl idx sid sst ();
            rewrite each sst' as st;
            assert session_state_related st (current_state t1);
            with pht. assert (models tbl pht);
            upd_singleton sid #t1 gsst;
            share_sid_pts_to sid #(next_trace t1 gsst);
            rewrite (session_state_related sst gsst) as
                    (session_state_related sst (current_state (next_trace t1 gsst)));
            fold pht_contains pht sid sst;
            fold (session_state_perm trace_ref pht sid);
            rewrite (session_state_perm trace_ref pht sid) as
                    (session_perm trace_ref pht (U16.v sid));
            frame_session_perm_on_range trace_ref pht0 pht 0 (U16.v sid);
            frame_session_perm_on_range trace_ref pht0 pht (U16.v sid + 1) (U16.v ctr);
            on_range_put 0 (U16.v sid) (U16.v ctr) #(session_perm trace_ref pht);
            let s = { st_ctr = ctr; st_tbl = tbl };
            rewrite each
              ctr as s.st_ctr,
              tbl as s.st_tbl;
            fold (dpe_inv trace_ref (Some s));
            mg := Some s;
            
            M.unlock (snd r) mg;
            drop_mutex_live (snd r) (dpe_inv trace_ref);

            st
          }
          None -> {
            unreachable ()
          }
        }
      } else {
        unfold sid_pts_to;
        gather_ trace_ref (sids_above_unused ctr) (singleton sid 0.5R t);
        unreachable ()
      }
    }
  }
}

#pop-options


fn init_engine_ctxt
  (uds:A.array U8.t { A.length uds == SZ.v uds_len })
  (#p:perm)
  (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  requires pts_to uds #p uds_bytes
  returns ctxt:context_t
  ensures pts_to uds #p uds_bytes **
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


let session_state_tag_related (s:session_state) (gs:g_session_state) : GTot bool =
  match s, gs with
  | SessionStart, G_SessionStart
  | InUse, G_InUse _
  | SessionClosed, G_SessionClosed _
  | SessionError, G_SessionError _
  | Available _, G_Available _ -> true
  | _ -> false



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

ghost fn unrelated_session_state #x #y ()
  requires session_state_related x y
  requires pure (match x, y with
    | SessionStart, G_SessionStart
    | InUse, G_InUse _
    | SessionClosed, G_SessionClosed _
    | SessionError, G_SessionError _
    | Available .., G_Available .. -> False
    | _ -> True)
  ensures pure False
{
  rewrite session_state_related x y as pure False;
}

#push-options "--fuel 2 --ifuel 2 --split_queries no"

fn initialize_context (sid:sid_t) 
  (t:G.erased trace { trace_valid_for_initialize_context t })
  (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  (uds:A.larray U8.t (SZ.v uds_len)) 
                       
  requires pts_to uds #p uds_bytes **
           sid_pts_to trace_ref sid t

  ensures pts_to uds #p uds_bytes **
          initialize_context_client_perm sid uds_bytes
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let s = replace_session sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to trace_ref sid t1);

  match s {
    SessionStart -> {
      rewrite (session_state_related SessionStart (current_state t)) as emp;
      let context = init_engine_ctxt uds;
      let s = Available { context };
      rewrite (context_perm context (Engine_context_repr uds_bytes)) as
              (session_state_related s (G_Available (Engine_context_repr uds_bytes)));
      let s = replace_session sid t1 s (G_Available (Engine_context_repr uds_bytes));
      intro_session_state_tag_related s (current_state t1);
      with _x _y. rewrite (session_state_related _x _y) as emp;
      fold (initialize_context_client_perm sid uds_bytes)
    }
    InUse -> {
      unrelated_session_state ();
      unreachable ()
    }
    SessionClosed -> {
      unrelated_session_state ();
      unreachable ()
    }
    SessionError -> {
      unrelated_session_state ();
      unreachable ()
    }
    Available _ -> {
      unrelated_session_state ();
      unreachable ()
    }
  }
}

#pop-options


fn init_l0_ctxt
  (cdi:A.array U8.t { A.length cdi == SZ.v dice_digest_len })
  (#engine_repr:erased engine_record_repr)
  (#s:erased (Seq.seq U8.t))
  (#uds_bytes:erased (Seq.seq U8.t))
  (_:squash (cdi_functional_correctness s uds_bytes engine_repr /\
             l0_is_authentic engine_repr))
  requires pts_to cdi s
  returns ctxt:l0_context_t
  ensures
    pts_to cdi s **
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



fn init_l1_ctxt
  (cdi:erased (Seq.seq U8.t))
  (deviceID_label_len:(n:erased U32.t { valid_hkdf_lbl_len n }))
  (aliasKey_label_len:(n:erased U32.t { valid_hkdf_lbl_len n }))
  (deviceIDCSR_ingredients:erased deviceIDCSR_ingredients_t)
  (aliasKeyCRT_ingredients:erased aliasKeyCRT_ingredients_t)
  (deviceID_pub:V.lvec U8.t 32)
  (aliasKey_priv:V.lvec U8.t 32)
  (aliasKey_pub:V.lvec U8.t 32)
  (deviceIDCSR_len:(n:U32.t { valid_deviceIDCSR_ingredients deviceIDCSR_ingredients n }))
  (deviceIDCSR:V.lvec U8.t (U32.v deviceIDCSR_len))
  (aliasKeyCRT_len:(n:U32.t { valid_aliasKeyCRT_ingredients aliasKeyCRT_ingredients n }))
  (aliasKeyCRT:V.lvec U8.t (U32.v aliasKeyCRT_len))
  (repr:erased l0_record_repr_t)
  (#deviceID_pub_repr #aliasKey_pub_repr #aliasKey_priv_repr
   #deviceIDCSR_repr #aliasKeyCRT_repr:erased (Seq.seq U8.t))
  (_:squash (l0_post
     cdi
     repr.fwid
     deviceID_label_len
     repr.deviceID_label
     aliasKey_label_len
     repr.aliasKey_label
     deviceIDCSR_ingredients
     aliasKeyCRT_ingredients
     deviceID_pub_repr
     aliasKey_pub_repr
     aliasKey_priv_repr
     deviceIDCSR_len
     deviceIDCSR_repr
     aliasKeyCRT_len
     aliasKeyCRT_repr))
  requires pts_to deviceID_pub deviceID_pub_repr ** 
           pts_to aliasKey_pub aliasKey_pub_repr ** 
           pts_to aliasKey_priv aliasKey_priv_repr ** 
           pts_to deviceIDCSR deviceIDCSR_repr **
           pts_to aliasKeyCRT aliasKeyCRT_repr **
           pure (V.is_full_vec deviceID_pub /\
                 V.is_full_vec aliasKey_pub /\
                 V.is_full_vec aliasKey_priv /\
                 V.is_full_vec deviceIDCSR /\
                  V.is_full_vec aliasKeyCRT)
  returns ctxt:l1_context_t
  ensures 
    l1_context_perm ctxt (mk_l1_context_repr_t
      cdi deviceID_label_len aliasKey_label_len deviceIDCSR_ingredients aliasKeyCRT_ingredients
      deviceID_pub_repr aliasKey_pub_repr aliasKey_priv_repr
      deviceIDCSR_len deviceIDCSR_repr aliasKeyCRT_len aliasKeyCRT_repr repr)
{
  let ctxt = mk_l1_context_t
    deviceID_pub aliasKey_pub aliasKey_priv deviceIDCSR_len deviceIDCSR aliasKeyCRT_len aliasKeyCRT;
  
  let l1_ctxt_repr = hide (mk_l1_context_repr_t
    cdi deviceID_label_len aliasKey_label_len
    deviceIDCSR_ingredients aliasKeyCRT_ingredients
    deviceID_pub_repr aliasKey_pub_repr aliasKey_priv_repr
    deviceIDCSR_len deviceIDCSR_repr aliasKeyCRT_len aliasKeyCRT_repr
    repr);

  rewrite each
    deviceID_pub as ctxt.deviceID_pub,
    aliasKey_pub as ctxt.aliasKey_pub,
    aliasKey_priv as ctxt.aliasKey_priv,
    deviceIDCSR as ctxt.deviceIDCSR,
    aliasKeyCRT as ctxt.aliasKeyCRT;

  rewrite each
    cdi as l1_ctxt_repr.cdi,
    deviceID_pub_repr as l1_ctxt_repr.deviceID_pub,
    aliasKey_pub_repr as l1_ctxt_repr.aliasKey_pub,
    aliasKey_priv_repr as l1_ctxt_repr.aliasKey_priv,
    deviceIDCSR_repr as l1_ctxt_repr.deviceIDCSR,
    aliasKeyCRT_repr as l1_ctxt_repr.aliasKeyCRT;

  fold (l1_context_perm ctxt l1_ctxt_repr);
  ctxt
}



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
  rewrite (pts_to r1.fwid #p repr.fwid) as (pts_to r2.fwid #p repr.fwid);
  rewrite (pts_to r1.deviceID_label #p repr.deviceID_label)
       as (pts_to r2.deviceID_label #p repr.deviceID_label);
  rewrite (pts_to r1.aliasKey_label #p repr.aliasKey_label)
       as (pts_to r2.aliasKey_label #p repr.aliasKey_label);
  fold (l0_record_perm r2 p repr)
}


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

 
fn destroy_ctxt (ctxt:context_t) (#repr:erased context_repr_t)
  requires context_perm ctxt repr
  ensures emp
{
  match ctxt
  {
    Engine_context c ->
    {
      let uds = rewrite_context_perm_engine c;
      unfold (engine_context_perm c uds);
      V.free c.uds;
    }
    L0_context c ->
    {
      let r = rewrite_context_perm_l0 c;
      unfold (l0_context_perm c r);
      V.free c.cdi;
    }
    L1_context c ->
    {
      let r = rewrite_context_perm_l1 c;
      unfold (l1_context_perm c r);
      V.free c.deviceID_pub;
      V.free c.aliasKey_priv;
      V.free c.aliasKey_pub;
      V.free c.aliasKeyCRT;
      V.free c.deviceIDCSR;
    }
  }
}



fn derive_child_from_context
    (context:context_t)
    (record:record_t)
    (#record_repr: erased repr_t)
    (#context_repr:erased (context_repr_t))
    (_:squash (valid_context_and_record_for_derive_child context_repr record_repr))

  requires
    context_perm context context_repr **
    record_perm record 1.0R record_repr
  returns res:(option context_t)
  ensures
    maybe_context_perm context_repr record_repr res
{
  intro_context_and_repr_tag_related context context_repr;
  intro_record_and_repr_tag_related record 1.0R record_repr;
 
  match context {
    Engine_context c -> {
      match record {
        Engine_record r -> {
          let uds_bytes = rewrite_context_perm_engine c;
          unfold (engine_context_perm c uds_bytes);

          let engine_record_repr = rewrite_record_perm_engine r;

          let mut cdi = [| 0uy; dice_digest_len |];

          V.to_array_pts_to c.uds;
          let ret = EngineCore.engine_main cdi (V.vec_to_array c.uds) r;
          V.to_vec_pts_to c.uds;

          let r = fst ret;
          rewrite each fst ret as r;

          with s. assert (pts_to cdi s);
          fold (engine_context_perm c uds_bytes);
          rewrite (engine_context_perm c uds_bytes)
               as (context_perm (Engine_context c) context_repr);
          rewrite (engine_record_perm r 1.0R engine_record_repr)
               as (record_perm (Engine_record r) 1.0R record_repr);

          destroy_ctxt (Engine_context c);
          //
          // TODO: FIXME: deallocate
          //
          drop_ (record_perm (Engine_record r) 1.0R record_repr);
         
          match snd ret {
            DICE_SUCCESS -> {
              let l0_ctxt = init_l0_ctxt cdi #engine_record_repr #s #uds_bytes ();
              with l0_ctxt_repr. assert (l0_context_perm l0_ctxt l0_ctxt_repr);
              fold (context_perm (L0_context l0_ctxt) (L0_context_repr l0_ctxt_repr));
              fold (maybe_context_perm context_repr record_repr (Some (L0_context l0_ctxt)));
              let ret = Some (L0_context l0_ctxt);
              rewrite each
                Some (L0_context l0_ctxt) as ret;
              ret
            }

            DICE_ERROR -> {
              A.zeroize dice_digest_len cdi;
              let ret = None #context_t;
              rewrite emp as (maybe_context_perm context_repr record_repr ret);
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
          let cr = rewrite_context_perm_l0 c;
          unfold (l0_context_perm c cr);
          with s. assert (pts_to c.cdi s);

          let r0 = rewrite_record_perm_l0 r;
          unfold (l0_record_perm r 1.0R r0);

          let deviceID_pub = V.alloc 0uy (SZ.uint_to_t 32);
          let aliasKey_pub = V.alloc 0uy (SZ.uint_to_t 32);
          let aliasKey_priv = V.alloc 0uy (SZ.uint_to_t 32);
          let deviceIDCSR_len = L0Types.len_of_deviceIDCSR r.deviceIDCSR_ingredients;
          let aliasKeyCRT_len = L0Types.len_of_aliasKeyCRT r.aliasKeyCRT_ingredients;
          let deviceIDCSR = V.alloc 0uy (SZ.uint32_to_sizet deviceIDCSR_len);
          let aliasKeyCRT = V.alloc 0uy (SZ.uint32_to_sizet aliasKeyCRT_len);

          V.to_array_pts_to c.cdi;
          V.to_array_pts_to r.fwid;
          V.to_array_pts_to r.deviceID_label;
          V.to_array_pts_to r.aliasKey_label;
          V.to_array_pts_to deviceID_pub;
          V.to_array_pts_to aliasKey_pub;
          V.to_array_pts_to aliasKey_priv;
          V.to_array_pts_to deviceIDCSR;
          V.to_array_pts_to aliasKeyCRT;

          HACL.reveal_dice_digest_len ();

          let _ : unit = l0
            (V.vec_to_array c.cdi)
            (V.vec_to_array r.fwid)
            r.deviceID_label_len
            (V.vec_to_array r.deviceID_label)
            r.aliasKey_label_len
            (V.vec_to_array r.aliasKey_label)
            r.deviceIDCSR_ingredients
            r.aliasKeyCRT_ingredients
            (V.vec_to_array deviceID_pub)
            (V.vec_to_array aliasKey_pub)
            (V.vec_to_array aliasKey_priv)
            deviceIDCSR_len
            (V.vec_to_array deviceIDCSR)
            aliasKeyCRT_len
            (V.vec_to_array aliasKeyCRT);
          
          V.to_vec_pts_to c.cdi;
          V.to_vec_pts_to r.fwid;
          V.to_vec_pts_to r.deviceID_label;
          V.to_vec_pts_to r.aliasKey_label;
          V.to_vec_pts_to deviceID_pub;
          V.to_vec_pts_to aliasKey_pub;
          V.to_vec_pts_to aliasKey_priv;
          V.to_vec_pts_to deviceIDCSR;
          V.to_vec_pts_to aliasKeyCRT;

          with deviceID_pub_repr. assert (pts_to deviceID_pub deviceID_pub_repr);
          with aliasKey_pub_repr. assert (pts_to aliasKey_pub aliasKey_pub_repr);
          with aliasKey_priv_repr. assert (pts_to aliasKey_priv aliasKey_priv_repr);
          with deviceIDCSR_repr. assert (pts_to deviceIDCSR deviceIDCSR_repr);
          with aliasKeyCRT_repr. assert (pts_to aliasKeyCRT aliasKeyCRT_repr);

          let l1_context : l1_context_t = init_l1_ctxt
            s
            (hide r.deviceID_label_len)
            (hide r.aliasKey_label_len)
            (hide r.deviceIDCSR_ingredients)
            (hide r.aliasKeyCRT_ingredients)
            deviceID_pub
            aliasKey_priv
            aliasKey_pub
            deviceIDCSR_len
            deviceIDCSR
            aliasKeyCRT_len
            aliasKeyCRT
            r0
            #deviceID_pub_repr #aliasKey_pub_repr #aliasKey_priv_repr
            #deviceIDCSR_repr #aliasKeyCRT_repr
            ();

          fold (l0_context_perm c cr);
          rewrite (l0_context_perm c cr) as
                  (context_perm (L0_context c) context_repr);
          fold (l0_record_perm r 1.0R r0);
          rewrite (l0_record_perm r 1.0R r0) as
                  (record_perm (L0_record r) 1.0R record_repr);

          destroy_ctxt (L0_context c);
          drop_ (record_perm (L0_record r) 1.0R record_repr);
                    
          with l1_context_repr. assert (l1_context_perm l1_context l1_context_repr);
          
          fold (context_perm (L1_context l1_context) (L1_context_repr l1_context_repr));

          fold (maybe_context_perm context_repr record_repr (Some (L1_context l1_context)));
          let ret = Some (L1_context l1_context);
          rewrite each
            Some (L1_context l1_context) as ret;

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



ghost
fn rewrite_session_state_related_available
  context
  (s:session_state { s == Available { context } })
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


#push-options "--fuel 2 --ifuel 2 --split_queries no --z3rlimit_factor 4"
#restart-solver
fn derive_child (sid:sid_t)
  (t:G.erased trace)
  (record:record_t)
  (#rrepr:erased repr_t { trace_and_record_valid_for_derive_child t rrepr })
  requires record_perm record 1.0R rrepr **
           sid_pts_to trace_ref sid t
  returns b:bool
  ensures derive_child_client_perm sid t rrepr b
{
  intro_record_and_repr_tag_related record 1.0R rrepr;

  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let s = replace_session sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to trace_ref sid t1);

  match s {
    Available hc -> {
      match hc.context {
        L1_context _ -> {
          rewrite (session_state_related (Available hc) (current_state t)) as
                  (pure False);
          unreachable ()
        }
        Engine_context _ -> {
          let repr = rewrite_session_state_related_available hc.context (Available hc) t;
          intro_context_and_repr_tag_related hc.context repr;
          let ret = derive_child_from_context hc.context record #rrepr #repr ();

          match ret {
            Some nctxt -> {
              unfold (maybe_context_perm repr rrepr (Some nctxt));
              with nrepr. assert (context_perm nctxt nrepr);
              intro_context_and_repr_tag_related nctxt nrepr;
              let s = Available { context = nctxt };
              rewrite (context_perm nctxt nrepr) as
                      (session_state_related s (G_Available nrepr));
              let s = replace_session sid t1 s (G_Available nrepr);
              intro_session_state_tag_related s (current_state t1);
              fold (derive_child_client_perm sid t rrepr true);
              with _x _y. rewrite (session_state_related _x _y) as emp;
              true
            }
            None -> {
              let s = SessionError;
              rewrite (maybe_context_perm repr rrepr None) as emp;
              rewrite emp as (session_state_related s (G_SessionError (current_state t1)));
              let s = replace_session sid t1 s (G_SessionError (current_state t1));
              intro_session_state_tag_related s (current_state t1);
              fold (derive_child_client_perm sid t rrepr false);
              with _x _y. rewrite (session_state_related _x _y) as emp;
              false
            }
          }
        }
        L0_context _ -> {
          let repr = rewrite_session_state_related_available hc.context (Available hc) t;
          intro_context_and_repr_tag_related hc.context repr;
          let ret = derive_child_from_context hc.context record #rrepr #repr ();

          match ret {
            Some nctxt -> {
              unfold (maybe_context_perm repr rrepr (Some nctxt));
              with nrepr. assert (context_perm nctxt nrepr);
              intro_context_and_repr_tag_related nctxt nrepr;
              let s = Available { context = nctxt };
              rewrite (context_perm nctxt nrepr) as
                      (session_state_related s (G_Available nrepr));
              let s = replace_session sid t1 s (G_Available nrepr);
              intro_session_state_tag_related s (current_state t1);
              fold (derive_child_client_perm sid t rrepr true);
              with _x _y. rewrite (session_state_related _x _y) as emp;
              true
            }
            None -> {
              let s = SessionError;
              rewrite (maybe_context_perm repr rrepr None) as emp;
              rewrite emp as (session_state_related s (G_SessionError (current_state t1)));
              let s = replace_session sid t1 s (G_SessionError (current_state t1));
              intro_session_state_tag_related s (current_state t1);
              fold (derive_child_client_perm sid t rrepr false);
              with _x _y. rewrite (session_state_related _x _y) as emp;
              false
            }
          }
        }

      }
    }
    SessionStart -> {
      unrelated_session_state ();
      unreachable ()
    }
    InUse -> {
      unrelated_session_state ();
      unreachable ()
    }
    SessionClosed -> {
      unrelated_session_state ();
      unreachable ()
    }
    SessionError -> {
      unrelated_session_state ();
      unreachable ()
    }
  }
}
#pop-options


fn destroy_session_state (s:session_state) (t:G.erased trace)
  requires session_state_related s (current_state t)
  ensures emp
{
  intro_session_state_tag_related s (current_state t);
  match s {
    Available hc -> {
      rewrite_session_state_related_available hc.context (Available hc) t;
      destroy_ctxt hc.context
    }
    SessionStart -> {
      with _x _y. rewrite (session_state_related _x _y) as emp
    }
    InUse -> {
      with _x _y. rewrite (session_state_related _x _y) as emp
    }
    SessionClosed -> {
      with _x _y. rewrite (session_state_related _x _y) as emp
    }
    SessionError -> {
      with _x _y. rewrite (session_state_related _x _y) as emp
    }

  }
}



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


#push-options "--z3rlimit_factor 4 --fuel 2 --ifuel 1 --split_queries no"

fn certify_key (sid:sid_t)
  (pub_key:A.larray U8.t 32)
  (crt_len:U32.t)
  (crt:A.larray U8.t (U32.v crt_len))
  (t:G.erased trace { trace_valid_for_certify_key t })
requires
  sid_pts_to trace_ref sid t **
  (exists* pub_key_repr crt_repr.
    pts_to pub_key pub_key_repr **
    pts_to crt crt_repr)
returns _:U32.t
ensures
  certify_key_client_perm sid t **
  (exists* pub_key_repr crt_repr.
      pts_to pub_key pub_key_repr **
      pts_to crt crt_repr)
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let s = replace_session sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to trace_ref sid t1);

  match s {
    norewrite Available hc -> {
      match hc.context {
        L1_context c -> {
          let c_crt_len = c.aliasKeyCRT_len;
          if U32.lt crt_len c_crt_len {
            let ns = Available { context = L1_context c };
            rewrite (session_state_related s (current_state t)) as
                    (session_state_related ns (current_state t));
            let s = replace_session sid t1 ns (current_state t);
            intro_session_state_tag_related s (current_state t1);
            with _x _y. rewrite (session_state_related _x _y) as emp;
            fold (certify_key_client_perm sid t);
            0ul
          } else {
            let r = rewrite_session_state_related_available (L1_context c) s t;
            let r = rewrite_context_perm_l1 c;
            unfold (l1_context_perm c r);

            V.to_array_pts_to c.aliasKey_pub;
            memcpy_l (SZ.uint_to_t 32) (V.vec_to_array c.aliasKey_pub) pub_key;
            V.to_vec_pts_to c.aliasKey_pub;

            V.to_array_pts_to c.aliasKeyCRT;
            
            memcpy_l (SZ.uint32_to_sizet c.aliasKeyCRT_len) (V.vec_to_array c.aliasKeyCRT) crt;
            V.to_vec_pts_to c.aliasKeyCRT;

            fold (l1_context_perm c r);
            rewrite (l1_context_perm c r) as
                    (context_perm (L1_context c) (L1_context_repr r));
            
            let ns = Available { context = L1_context c };
            rewrite (context_perm (L1_context c) (L1_context_repr r)) as
                    (session_state_related ns (current_state t));
            
            let s = replace_session sid t1 ns (current_state t);
            intro_session_state_tag_related s (current_state t1);
            with _x _y. rewrite (session_state_related _x _y) as emp;
            fold (certify_key_client_perm sid t);
            c_crt_len
          }
        }
        L0_context _ -> {
          rewrite (session_state_related s (current_state t)) as
                  (pure False);
          unreachable ()
        }
        Engine_context _ -> {
          rewrite (session_state_related s (current_state t)) as
                  (pure False);
          unreachable ()
        }

      }
    }
    SessionStart -> {
      unrelated_session_state ();
      unreachable ()
    }
    InUse -> {
      unrelated_session_state ();
      unreachable ()
    }
    SessionClosed -> {
      unrelated_session_state ();
      unreachable ()
    }
    SessionError -> {
      unrelated_session_state ();
      unreachable ()
    }
  }
}

#pop-options

#push-options "--split_queries no"

fn sign (sid:sid_t)
  (signature:A.larray U8.t 64)
  (msg_len:SZ.t { SZ.v msg_len < pow2 32 })
  (msg:A.larray U8.t (SZ.v msg_len))
  (t:G.erased trace { trace_valid_for_sign t })
requires 
  sid_pts_to trace_ref sid t **
  (exists* signature_repr msg_repr.
    pts_to signature signature_repr **
    pts_to msg msg_repr)
ensures
  sign_client_perm sid t **
  (exists* signature_repr msg_repr.
      pts_to signature signature_repr **
      pts_to msg msg_repr)
{
  rewrite emp as (session_state_related InUse (G_InUse (current_state t)));
  let s = replace_session sid t InUse (G_InUse (current_state t));
  with t1. assert (sid_pts_to trace_ref sid t1);

  match s {
    norewrite Available hc -> {
      match hc.context {
        L1_context c -> {
          let r = rewrite_session_state_related_available (L1_context c) s t;
          let r = rewrite_context_perm_l1 c;
          unfold (l1_context_perm c r);

          V.to_array_pts_to c.aliasKey_priv;
          HACL.ed25519_sign signature (V.vec_to_array c.aliasKey_priv) msg_len msg;
          V.to_vec_pts_to c.aliasKey_priv;

          fold (l1_context_perm c r);
          rewrite (l1_context_perm c r) as
                  (context_perm (L1_context c) (L1_context_repr r));
            
          let ns = Available { context = L1_context c };
          rewrite (context_perm (L1_context c) (L1_context_repr r)) as
                  (session_state_related ns (current_state t));
            
          let s = replace_session sid t1 ns (current_state t);
          intro_session_state_tag_related s (current_state t1);
          with _x _y. rewrite (session_state_related _x _y) as emp;
          fold (sign_client_perm sid t);
        }
        L0_context _ -> {
          rewrite (session_state_related s (current_state t)) as
                  (pure False);
          unreachable ()
        }
        Engine_context _ -> {
          rewrite (session_state_related s (current_state t)) as
                  (pure False);
          unreachable ()
        }
      }
    }
    SessionStart -> {
      unrelated_session_state ();
      unreachable ()
    }
    InUse -> {
      unrelated_session_state ();
      unreachable ()
    }
    SessionClosed -> {
      unrelated_session_state ();
      unreachable ()
    }
    SessionError -> {
      unrelated_session_state ();
      unreachable ()
    }

  }
}

#pop-options

(*
  GetProfile: Part of DPE API 
  Get the DPE's profile. 
*)

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
