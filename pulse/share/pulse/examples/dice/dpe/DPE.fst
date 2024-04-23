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

module L = Pulse.Lib.SpinLock
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HT = Pulse.Lib.HashTable
module PHT = Pulse.Lib.HashTable.Spec

// open Pulse.Lib.BoundedIntegers
open Pulse.Lib.OnRange
open Pulse.Lib.HashTable.Type
open Pulse.Lib.HashTable
open Pulse.Lib.Mutex

// noeq
// type cell (a:Type0) = {
//   v : a;
//   next : ref (cell a);
//   lock : L.lock;
// }

// let rec llist (#a:Type) (cref:ref (cell a)) (repr:list a) : Tot vprop (decreases repr) =
//   match repr with
//   | [] -> emp
//   | hd::tl ->
//     exists* c.
//     pts_to cref #0.5R c **
//     pure (hd == c.v) **
//     L.lock_alive c.lock (exists* cnext. pts_to c.next cnext) **
//     llist c.next tl


assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a

(* Global State *)

let ctxt_hndl_t = U32.t

type sid_t : eqtype = U32.t

[@@ Rust_derive "Clone"]
noeq
type session_state =
  | SessionStart
  | Available { handle:ctxt_hndl_t; context:context_t }
  | InUse
  | SessionClosed
  | SessionError //error description

//
// These two definitions extract to non-exhaustive patterns in Rust
//   which fails to typecheck
//
noextract
let ctxt_of (s:session_state { Available? s })
  : context_t
  = let Available {context} = s in
    context

noextract
let hndl_of (s:session_state { Available? s })
  : ctxt_hndl_t
  = let Available { handle } = s in handle

let mk_available (hndl:ctxt_hndl_t) (ctxt:context_t)
  : session_state
  = Available { handle = hndl; context = ctxt }

// Marking this noextract since this spec only
// What will krml do?

noextract
type ht_t = ht_t sid_t session_state

noextract
type pht_t = PHT.pht_t sid_t session_state

noeq
type st = { st_ctr:sid_t; st_tbl:ht_t; }

module G = FStar.Ghost
module PP = PulseCore.Preorder
module PM = Pulse.Lib.PCMMap
module T = DPE.Trace
module PCM = FStar.PCM

type pcm_t : Type u#1 = PM.map sid_t (T.pcm_t)
let pcm : PCM.pcm pcm_t = PM.pointwise sid_t T.pcm
type gref = ghost_pcm_ref pcm

let emp_trace : T.trace = []

let singleton (sid:sid_t) (p:perm) (t:T.trace) : pcm_t =
  Map.upd (Map.const (None, emp_trace)) sid (Some p, t)

let sid_pts_to (r:gref) (sid:sid_t) (t:T.trace) : vprop =
  ghost_pcm_pts_to r (singleton sid 0.5R t)

let session_state_tag_related (s:session_state) (gs:T.g_session_state) : GTot bool =
  let open T in
  match s, gs with
  | SessionStart, G_SessionStart
  | InUse, G_InUse _
  | SessionClosed, G_SessionClosed _
  | SessionError, G_SessionError _
  | Available _, G_Available _ -> true
  | _ -> false

let session_state_related (s:session_state) (gs:T.g_session_state) : vprop =
  let open T in
  match s, gs with
  | SessionStart, G_SessionStart
  | InUse, G_InUse _
  | SessionClosed, G_SessionClosed _
  | SessionError, G_SessionError _ -> emp

  | Available _, G_Available repr -> context_perm (ctxt_of s) repr

  | _ -> pure False

let session_state_perm (r:gref) (pht:pht_t) (sid:sid_t) =
  exists* (s:session_state) (t:T.trace). pure (PHT.lookup pht sid == Some s) **
                                         sid_pts_to r sid t **
                                         session_state_related s (T.current_state t)

let session_perm (r:gref) (pht:pht_t) (sid:nat) =
  if UInt.fits sid 32
  then session_state_perm r pht (U32.uint_to_t sid)
  else emp

let map_literal (f:sid_t -> T.pcm_t) = Map.map_literal f

let all_sids_unused : pcm_t = map_literal (fun _ -> Some 1.0R, emp_trace)

let sids_above_unused (s:sid_t) : pcm_t = map_literal (fun sid ->
  if U32.lt sid s then None, emp_trace
  else Some 1.0R, emp_trace)

let inv (r:gref) (s:option st) : vprop =
  match s with
  | None -> ghost_pcm_pts_to r all_sids_unused
  
  | Some s ->
    ghost_pcm_pts_to r (sids_above_unused s.st_ctr) **
    
    (exists* pht. models s.st_tbl pht **
                  on_range (session_perm r pht) 0 (U32.v s.st_ctr))

type dpe_t = gref & mutex (option st)

let dpe_inv (s:dpe_t) = mutex_live (snd s) (inv (fst s))

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


let full (t0:T.trace) = Some #perm 1.0R, t0
let half (t0:T.trace) = Some #perm 0.5R, t0

```pulse
ghost
fn upd_sid_pts_to
  (r:gref) (sid:sid_t)
  (#t0 #t1:T.trace)
  (s:T.g_session_state { T.valid_transition t0 s })

  requires sid_pts_to r sid t0 **
           sid_pts_to r sid t1
  ensures sid_pts_to r sid (T.next_trace t0 s) **
          sid_pts_to r sid (T.next_trace t0 s) **
          pure (t0 == t1)
{
  unfold sid_pts_to;
  unfold sid_pts_to;

  gather_v r (singleton sid 0.5R t0)
             (singleton sid 0.5R t1)
             (singleton sid 1.0R t0);

  let fp : PCM.frame_preserving_upd T.pcm (full t0) (full (T.next_trace t0 s)) =
    T.mk_frame_preserving_upd t0 s;

  assert (pure (Map.equal (Map.upd (singleton sid 1.0R t0) sid (full (T.next_trace t0 s)))
                          (singleton sid 1.0R (T.next_trace t0 s))));

  let fp : PCM.frame_preserving_upd pcm (singleton sid 1.0R t0) (singleton sid 1.0R (T.next_trace t0 s)) =
    PM.lift_frame_preserving_upd #_ #_ #T.pcm
      (full t0)
      (full (T.next_trace t0 s))
      fp
      (singleton sid 1.0R t0) sid;

  ghost_write r
    (singleton sid 1.0R t0)
    (singleton sid 1.0R (T.next_trace t0 s))
    fp;

  share_ r (singleton sid 1.0R (T.next_trace t0 s))
           (singleton sid 0.5R (T.next_trace t0 s))
           (singleton sid 0.5R (T.next_trace t0 s));

  fold (sid_pts_to r sid (T.next_trace t0 s));
  fold (sid_pts_to r sid (T.next_trace t0 s));
}
```

assume val sid_hash : sid_t -> SZ.t

[@@ Rust_const_fn]
```pulse
fn initialize_global_state ()
  requires emp
  returns s:dpe_t
  ensures dpe_inv s
{
  let r = ghost_alloc #_ #pcm all_sids_unused;
  with _v. rewrite (ghost_pcm_pts_to r (G.reveal (G.hide _v))) as
                   (ghost_pcm_pts_to r _v);
  fold (inv r None);
  assume_ (pure (forall s. is_big (inv r s)));
  let m = new_mutex (inv r) None;
  let s = ((r, m) <: dpe_t);
  rewrite each r as fst s;
  rewrite each m as snd s;
  fold (dpe_inv s);
  s
}
```

let global_state : dpe_t = run_stt (initialize_global_state ())

assume val safe_add (i j:U32.t)
  : o:option U32.t { Some? o ==> U32.v (Some?.v o) == U32.v i + U32.v j }

(* Utilities to work with on_range (session_perm stm) *)
(* <utilities on on_range> *)
noextract  // TODO: why do we extract this at all, it is a prop
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

(* </utilities on on_range> *)

let open_session_client_perm (r:gref) (s:option sid_t) : vprop =
  match s with
  | None -> emp
  | Some s ->
    exists* t. sid_pts_to r s t ** pure (T.current_state t == T.G_SessionStart)

let emp_to_start_valid () : Lemma (T.valid_transition emp_trace T.G_SessionStart) = ()

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
      if not b {
        let s = { st_ctr = ctr; st_tbl = tbl1 };
        let ret = s, None #sid_t;
        rewrite each
          tbl1 as (fst ret).st_tbl,
          pht1 as pht,
          ctr as (fst ret).st_ctr;
        fold (inv r (Some (fst ret)));
        rewrite emp as (open_session_client_perm r (snd ret));
        ret        
      } else {
        share_ r (sids_above_unused ctr)
                 (sids_above_unused ctr1)
                 (singleton ctr 1.0R emp_trace);
        share_ r (singleton ctr 1.0R emp_trace)
                 (singleton ctr 0.5R emp_trace)
                 (singleton ctr 0.5R emp_trace);
        fold (sid_pts_to r ctr emp_trace);
        fold (sid_pts_to r ctr emp_trace);
        emp_to_start_valid ();
        upd_sid_pts_to r ctr #emp_trace #emp_trace T.G_SessionStart;
        rewrite emp as (session_state_related SessionStart T.G_SessionStart);
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
  let mr = lock m;
  let sopt = R.replace mr None;

  let s = maybe_mk_session_tbl r sopt;
  let ret = __open_session r s;
  let s = fst ret;
  let sid_opt = snd ret;
  rewrite each
    fst ret as s,
    snd ret as sid_opt;
  mr := Some s;
  unlock m mr;

  let ret = (m, sid_opt);

  rewrite each
    m as fst ret,
    sid_opt as snd ret;
  ret
}
```

```pulse
ghost
fn gather_sid_pts_to (r:gref) (sid:sid_t) (#t0 #t1:T.trace)
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
fn share_sid_pts_to (r:gref) (sid:sid_t) (#t:T.trace)
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
  (#t:T.trace)
  (s:T.g_session_state { T.valid_transition t s })
  requires ghost_pcm_pts_to r (singleton sid 1.0R t)
  ensures ghost_pcm_pts_to r (singleton sid 1.0R (T.next_trace t s))
{
  let fp : PCM.frame_preserving_upd T.pcm (full t) (full (T.next_trace t s)) =
    T.mk_frame_preserving_upd t s;

  assert (pure (Map.equal (Map.upd (singleton sid 1.0R t) sid (full (T.next_trace t s)))
                          (singleton sid 1.0R (T.next_trace t s))));

  let fp : PCM.frame_preserving_upd pcm (singleton sid 1.0R t) (singleton sid 1.0R (T.next_trace t s)) =
    PM.lift_frame_preserving_upd #_ #_ #T.pcm
      (full t)
      (full (T.next_trace t s))
      fp
      (singleton sid 1.0R t) sid;

  ghost_write r
    (singleton sid 1.0R t)
    (singleton sid 1.0R (T.next_trace t s))
    fp;
}
```

#push-options "--fuel 0 --ifuel 2 --split_queries no --z3rlimit_factor 2"
```pulse
fn replace_session
  (r:gref)
  (m:mutex (option st))
  (sid:sid_t)
  (t:T.trace)
  (sst:session_state)
  (gsst:T.g_session_state { T.valid_transition t gsst})

  requires mutex_live m (inv r) **
           sid_pts_to r sid t **
           session_state_related sst gsst

  returns b:(mutex (option st) & session_state)

  ensures mutex_live (fst b) (inv r) **
          session_state_related (snd b) (T.current_state t) **
          sid_pts_to r sid (T.next_trace t gsst)
{
  let mr = lock m;
  let sopt = R.replace mr None;
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
              with _s. rewrite (session_state_related _s (T.current_state t1)) as
                               (session_state_related st (T.current_state t1));
              with pht. assert (models tbl pht);
              upd_singleton r sid #t1 gsst;
              share_sid_pts_to r sid;
              rewrite (session_state_related sst gsst) as
                      (session_state_related sst (T.current_state (T.next_trace t1 gsst)));
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
              mr := Some s;
              unlock m mr;
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
          admit ()
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

module V = Pulse.Lib.Vec

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

```pulse
ghost
fn intro_session_state_tag_related (s:session_state) (gs:T.g_session_state)
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

let trace_valid_for_initialize_context (t:T.trace) =
  T.current_state t == T.G_SessionStart

let initialize_context_client_perm (r:gref) (sid:sid_t) (uds:Seq.seq U8.t) =
  exists* t. sid_pts_to r sid t **
             pure (T.current_state t == T.G_Available (Engine_context_repr uds))

#push-options "--fuel 2 --ifuel 2 --split_queries no"
```pulse
fn initialize_context (r:gref) (m:mutex (option st))
  (sid:sid_t) 
  (t:T.trace { trace_valid_for_initialize_context t })
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
  rewrite emp as (session_state_related InUse (T.G_InUse (T.current_state t)));
  let ret = replace_session r m sid t InUse (T.G_InUse (T.current_state t));
  with t1. assert (sid_pts_to r sid t1);

  let m = fst ret;
  let s = snd ret;

  rewrite each
    fst ret as m,
    snd ret as s;
  
  match s {
    SessionStart -> {
      rewrite (session_state_related s (T.current_state t)) as emp;
      let context = init_engine_ctxt uds;
      let handle = prng ();
      let s = Available { handle; context };
      rewrite (context_perm context (Engine_context_repr uds_bytes)) as
              (session_state_related s (T.G_Available (Engine_context_repr uds_bytes)));
      let ret = replace_session r m sid t1 s (T.G_Available (Engine_context_repr uds_bytes));
      intro_session_state_tag_related (snd ret) (T.current_state t1);
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
      rewrite (session_state_related s (T.current_state t)) as
              (pure False);
      unreachable ()
    }
    SessionClosed -> {
      rewrite (session_state_related s (T.current_state t)) as
              (pure False);
      unreachable ()
    }
    SessionError -> {
      rewrite (session_state_related s (T.current_state t)) as
              (pure False);
      unreachable ()
    }
    Available _ -> {
      rewrite (session_state_related s (T.current_state t)) as
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
              
  requires A.pts_to deviceID_priv deviceID_priv0 ** 
           A.pts_to deviceID_pub deviceID_pub0 ** 
           A.pts_to aliasKey_priv aliasKey_priv0 ** 
           A.pts_to aliasKey_pub aliasKey_pub0 ** 
           A.pts_to deviceIDCSR deviceIDCSR0 **
           A.pts_to aliasKeyCRT aliasKeyCRT0 **
           pure (
            valid_hkdf_ikm_len dice_digest_len
                       /\ aliasKey_functional_correctness
                            dice_hash_alg dice_digest_len cdi repr.fwid
                            aliasKey_label_len repr.aliasKey_label 
                            aliasKey_pub0 aliasKey_priv0
                       /\ deviceIDCSR_functional_correctness 
                            dice_hash_alg dice_digest_len cdi
                            deviceID_label_len repr.deviceID_label deviceIDCSR_ingredients 
                            deviceIDCSR_len deviceIDCSR0 
                       /\ aliasKeyCRT_functional_correctness 
                            dice_hash_alg dice_digest_len cdi repr.fwid
                            deviceID_label_len repr.deviceID_label aliasKeyCRT_ingredients 
                            aliasKeyCRT_len aliasKeyCRT0 aliasKey_pub0
           )
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

let next_context (oc:context_t) (c:context_t) : prop =
  match oc, c with
  | Engine_context _, L0_context _
  | L0_context _, L1_context _ -> True
  | _ -> False

let maybe_context_perm (oc:context_t) (c:option context_t) =
  match c with
  | Some c ->
    pure (next_context oc c) ** (exists* repr. context_perm c repr)
  | None -> emp

let valid_context_and_record_for_derive_child (c:context_t) (r:record_t) : prop =
  match c, r with
  | Engine_context _, Engine_record _ -> True
  | L0_context _, L0_record _ -> True
  | _ -> False

```pulse
fn derive_child_from_context
    (context:context_t)
    (record:record_t)
    p
    (#record_repr: erased repr_t)
    (#context_repr:erased (context_repr_t))
    (_:squash (valid_context_and_record_for_derive_child context record))

  requires
    context_perm context context_repr **
    record_perm record p record_repr
  returns res:(context_t & record_t & option context_t)
  ensures
    context_perm (tfst res) context_repr **
    record_perm (tsnd res) p record_repr **
    maybe_context_perm context (tthd res)
{
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
          let succ = snd ret;
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
              fold (maybe_context_perm context (Some (L0_context l0_ctxt)));
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
              rewrite emp as (maybe_context_perm context (tthd ret));
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

          let l1_context = init_l1_ctxt 
                      deviceIDCSR_len aliasKeyCRT_len deviceID_priv deviceID_pub
                      aliasKey_priv aliasKey_pub (V.vec_to_array deviceIDCSR) (V.vec_to_array aliasKeyCRT)
                      (hide r2.deviceID_label_len)
                      (hide r2.aliasKey_label_len) s r0 (hide r2.deviceIDCSR_ingredients) (hide r2.aliasKeyCRT_ingredients);
          with l1_context_repr. assert (l1_context_perm l1_context l1_context_repr);
          fold (context_perm (L1_context l1_context) (L1_context_repr l1_context_repr));

          V.to_vec_pts_to deviceIDCSR;
          V.to_vec_pts_to aliasKeyCRT;
          V.free deviceIDCSR;
          V.free aliasKeyCRT;

          fold (maybe_context_perm context (Some (L1_context l1_context)));
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
  (t:T.trace)
  requires session_state_related s (T.current_state t)
  returns r:G.erased context_repr_t
  ensures context_perm context r ** pure (T.current_state t == T.G_Available r)
{
  let cur = T.current_state t;
  intro_session_state_tag_related s (T.current_state t);
  let repr = T.G_Available?.repr cur;
  rewrite (session_state_related s (T.current_state t)) as
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

let trace_and_record_valid_for_derive_child (t:T.trace) (r:record_t) : prop =
  let open T in
  match current_state t, r with
  | G_Available (Engine_context_repr _), Engine_record _
  | G_Available (L0_context_repr _), L0_record _ -> True
  | _ -> False

let derive_child_pre_post_traces (t0:T.trace) (t1:T.trace) =
  let open T in
  match current_state t0, current_state t1 with
  | G_Available (Engine_context_repr _), G_Available (L0_context_repr _)
  | G_Available (L0_context_repr _), G_Available (L1_context_repr _) -> True
  | _ -> False

let derive_child_client_perm (r:gref) (sid:sid_t) (t0:T.trace) (c:option ctxt_hndl_t) : vprop =
  match c with
  | None ->
    exists* t1. sid_pts_to r sid t1 **
                pure (T.current_state t1 == T.G_SessionError (T.G_InUse (T.current_state t0)))
  | Some _ ->
    exists* t1. sid_pts_to r sid t1 **
                pure (derive_child_pre_post_traces t0 t1)

(*
  DeriveChild: Part of DPE API 
  Execute the DICE layer associated with the current context and produce a 
  new context. Destroy the current context in the current session's context table 
  and store the new context in the table. Return the new context handle upon
  success and None upon failure. 
*)
#push-options "--fuel 2 --ifuel 2"
```pulse
fn derive_child (r:gref) (m:mutex (option st)) (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
  (t:T.trace)
  (record:record_t { trace_and_record_valid_for_derive_child t record })
  (#repr:erased repr_t) (#p:perm)
  requires mutex_live m (inv r) **
           record_perm record p repr **
           sid_pts_to r sid t
  returns b:(mutex (option st) & record_t & option ctxt_hndl_t)
  ensures mutex_live (tfst b) (inv r) **
          record_perm (tsnd b) p repr **
          derive_child_client_perm r sid t (tthd b)
{
  rewrite emp as (session_state_related InUse (T.G_InUse (T.current_state t)));
  let ret = replace_session r m sid t InUse (T.G_InUse (T.current_state t));
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
          rewrite (session_state_related s (T.current_state t)) as
                  (pure False);
          unreachable ()
        }
        _ -> {
          assume_ (pure (~ (L1_context? hc.context)));
          let repr = rewrite_session_state_related_available hc.handle hc.context s t;
          intro_context_and_repr_tag_related hc.context repr;
          let ret = derive_child_from_context hc.context record p ();

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
              unfold (maybe_context_perm hc.context (Some nctxt));
              with nrepr. assert (context_perm nctxt nrepr);
              intro_context_and_repr_tag_related nctxt nrepr;
              let handle = prng ();
              let s = Available { handle; context = nctxt };
              rewrite (context_perm nctxt nrepr) as
                      (session_state_related s (T.G_Available nrepr));
              let ret = replace_session r m sid t1 s (T.G_Available nrepr);
              intro_session_state_tag_related (snd ret) (T.current_state t1);
              let m = fst ret;
              rewrite each
                fst ret as m,
                snd ret as InUse;
              let ret = (m, record, Some handle);
              rewrite each
                m as tfst ret,
                record as tsnd ret;
              fold (derive_child_client_perm r sid t (Some handle));
              with _x _y. rewrite (session_state_related _x _y) as emp;
              ret
            }
            None -> {
              let s = SessionError;
              rewrite emp as (session_state_related s (T.G_SessionError (T.current_state t1)));
              let ret = replace_session r m sid t1 s (T.G_SessionError (T.current_state t1));
              intro_session_state_tag_related (snd ret) (T.current_state t1);
              let m = fst ret;
              rewrite each
                fst ret as m,
                snd ret as InUse;
              let ret = (m, record, None #ctxt_hndl_t);
              rewrite each
                m as tfst ret,
                record as tsnd ret;
              rewrite (maybe_context_perm hc.context nctxt) as emp;
              fold (derive_child_client_perm r sid t None);
              with _x _y. rewrite (session_state_related _x _y) as emp;
              ret
            }
          }
        }
      }
    }
    SessionStart -> {
      rewrite (session_state_related s (T.current_state t)) as
              (pure False);
      unreachable ()
    }
    InUse -> {
      rewrite (session_state_related s (T.current_state t)) as
              (pure False);
      unreachable ()
    }
    SessionClosed -> {
      rewrite (session_state_related s (T.current_state t)) as
              (pure False);
      unreachable ()
    }
    SessionError -> {
      rewrite (session_state_related s (T.current_state t)) as
              (pure False);
      unreachable ()
    }
  }
}
```

let trace_valid_for_close (t:T.trace) : prop =
  let open T in
  match current_state t with
  | G_UnInitialized
  | G_SessionClosed _
  | G_InUse _ -> False
  | _ -> True

(* 
  CloseSession: Part of DPE API 
  Destroy the context table for the session and remove the reference
  to it from the session table. Return boolean indicating success. 
  NOTE: Current implementation disregards session protocol 
*)

let session_closed_client_perm (r:gref) (sid:sid_t) (t0:T.trace) =
  exists* t1. sid_pts_to r sid t1 **
              pure (T.current_state t1 == T.G_SessionClosed (T.G_InUse (T.current_state t0)))

```pulse
fn destroy_session_state (s:session_state) (t:T.trace)
  requires session_state_related s (T.current_state t)
  ensures emp
{
  intro_session_state_tag_related s (T.current_state t);
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
  (t:T.trace { trace_valid_for_close t })
  requires mutex_live m (inv r) **
           sid_pts_to r sid t
  returns m:mutex (option st)
  ensures mutex_live m (inv r) **
          session_closed_client_perm r sid t
{
  rewrite emp as (session_state_related InUse (T.G_InUse (T.current_state t)));
  let ret = replace_session r m sid t InUse (T.G_InUse (T.current_state t));
  with t1. assert (sid_pts_to r sid t1);

  let m = fst ret;
  let s = snd ret;
  rewrite each
    fst ret as m,
    snd ret as s;

  intro_session_state_tag_related s (T.current_state t);

  destroy_session_state s t;

  rewrite emp as (session_state_related SessionClosed (T.G_SessionClosed (T.current_state t1)));
  let ret = replace_session r m sid t1 SessionClosed (T.G_SessionClosed (T.current_state t1));
  intro_session_state_tag_related (snd ret) (T.current_state t1);
  let m = fst ret;
  rewrite each
    fst ret as m,
    snd ret as InUse;
  with _x _y. rewrite (session_state_related _x _y) as emp;
  fold (session_closed_client_perm r sid t);
  m
}
```

// #push-options "--ext 'pulse:env_on_err' --print_implicits --warn_error -342"

// (* ----------- IMPLEMENTATION ----------- *)

// (*
//   GetProfile: Part of DPE API 
//   Get the DPE's profile. 
// *)
// ```pulse
// fn get_profile ()
//   requires emp
//   returns d:profile_descriptor_t
//   ensures emp
// {
//   mk_profile_descriptor
//     (*name=*)""
//     (*dpe_spec_version=*)1ul
//     (*max_message_size=*)0ul // irrelevant: using direct interface
//     (*uses_multi_part_messages=*)false
//     (*supports_concurrent_operations=*)false // irrelevant by uses_multi_part_messages
//     (*supports_encrypted_sessions=*)false // irrelevant by uses_multi_part_messages
//     (*supports_derived_sessions=*)false // irrelevant by supports_encrypted_sessions
//     (*max_sessions=*)0sz // irrelevant by supports_encrypted_sessions
//     (*session_protocol=*)"" // irrelevant by supports_encrypted_sessions
//     (*supports_session_sync=*)false // by supports_encrypted_sessions
//     (*session_sync_policy=*)"" // irrelevant by supports_session_sync
//     (*session_migration_protocol=*)"" // irrelevant by supports_session_migration
//     (*supports_default_context=*)false
//     (*supports_context_handles=*)true 
//     (*max_contexts_per_session=*)1sz // 1 context per session
//     (*max_context_handle_size=*)16sz // 16 bits
//     (*supports_auto_init=*)false // irrelevant by supports_default_context
//     (*supports_simulation=*)false
//     (*supports_attestation=*)false
//     (*supports_sealing=*)false 
//     (*supports_get_profile=*)true
//     (*supports_open_session=*)false // irrelevant by supports_encrypted_sessions
//     (*supports_close_session=*)false // irrelevant by supports_encrypted_sessions
//     (*supports_sync_session=*)false // irrelevant by supports_encrypted_sessions
//     (*supports_export_session=*)false
//     (*supports_import_session=*)false
//     (*supports_init_context=*)true
//     (*supports_certify_key=*)false // irrelevant by supports_attestation
//     (*supports_sign=*)false // irrelevant by supports_attestation
//     (*supports_seal=*)false // irrelevant by supports_sealing
//     (*supports_unseal=*)false // irrelevant by supports_sealing
//     (*supports_sealing_public=*)false // irrelevant by supports_sealing
//     (*supports_rotate_context_handle=*)true
//     (*dice_derivation=*)"" // FIXME: name for DICE algorithms
//     (*asymmetric_derivation=*)"" // irrelevant by supports_attestation
//     (*symmetric_derivation=*)"" // irrelevant by supports_attestation
//     (*supports_any_label=*)false
//     (*supported_labels=*)"" // FIXME: what are lables?
//     (*initial_derivation=*)"" // FIXME: name?
//     (*input_format=*)"" // FIXME: create CDDL spec for input record formats
//     (*supports_internal_inputs=*)false
//     (*supports_internal_dpe_info=*)false // irrelevant by supports_internal_inputs
//     (*supports_internal_dpe_dice=*)false // irrelevant by supports_internal_inputs
//     (*internal_dpe_info_type=*)"" // irrelevant by supports_internal_inputs
//     (*internal_dpe_dice_type=*)"" // irrelevant by supports_internal_inputs
//     (*internal_inputs=*)"" // irrelevant by supports_internal_inputs
//     (*supports_certificates=*)false // irrelevant by supports_attestation
//     (*max_certificate_size=*)0sz // irrelevant by supports_certificates
//     (*max_certificate_chain_size=*)0sz // irrelevant by supports_certificates
//     (*appends_more_certificates=*)false // irrelevant by supports_certificates
//     (*supports_certificate_policies=*)false // irrelevant by supports_certificates
//     (*supports_policy_identity_init=*)false // irrelevant by supports_certificate_policies
//     (*supports_policy_identity_loc=*)false // irrelevant by supports_certificate_policies
//     (*supports_policy_attest_init=*)false // irrelevant by supports_certificate_policies
//     (*supports_policy_attest_loc=*)false // irrelevant by supports_certificate_policies
//     (*supports_policy_assert_init=*)false // irrelevant by supports_certificate_policies
//     (*supports_policy_assert_loc=*)false // irrelevant by supports_certificate_policies
//     (*certificate_policies=*)"" // irrelevant by supports_certificate_policies
//     (*supports_eca_certificates=*)false // irrelevant by supports_certificate_policies
//     (*eca_certificate_format=*)"" // irrelevant by supports_eca_certificates
//     (*leaf_certificate_format=*)"" // irrelevant by supports_certificates
//     (*public_key_format=*)"" // irrelevant by supports_asymmetric_unseal
//     (*supports_external_key=*)false // irrelevant by supports_certificates
//     (*to_be_signed_format=*)"" // irrelevant by supports_sign
//     (*signature_format=*)"" // irrelevant by supports_sign
//     (*supports_symmetric_sign=*)false // irrelevant by supports_attestation
//     (*supports_asymmetric_unseal=*)false // irrelevant by supports_attestation
//     (*supports_unseal_policy=*)false// irrelevant by supports_sealing
//     (*unseal_policy_format=*)"" // irrelevant by supports_unseal_policy 
// }
// ```
// // let get_profile = get_profile'
