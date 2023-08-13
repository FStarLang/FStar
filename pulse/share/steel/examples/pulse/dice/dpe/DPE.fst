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
open PulseHashTable
module PHT = PulseHashTable
module LSHT = LinearScanHashTable
open Pulse.Class.BoundedIntegers

assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a


(* ----------- GLOBAL STATE ----------- *)

let dpe_hashf : nat -> US.t = admit()
let sht_len : pos_us = admit()
let cht_len : pos_us = admit()

// A table whose permission is stored in the lock 

```pulse
fn alloc_ht (#s:pht_sig_us) (l:pos_us)
  requires emp
  returns _:locked_ht_t s
  ensures emp
{
  let contents = A.alloc #(cell s.keyt s.valt) Clean l;
  let ht = mk_ht l contents;
  let pht = mk_init_pht #s l;
  rewrite (A.pts_to contents (Seq.create (US.v l) Clean))
    as (A.pts_to ht.contents pht.repr);
  fold (models s ht pht);
  fold (ht_perm s ht);
  let lk = L.new_lock (ht_perm s ht);
  ((| ht, lk |) <: locked_ht_t s)
}
```
let locked_sht : locked_ht_t sht_sig = run_stt(alloc_ht #sht_sig sht_len)

// A number that tracks the next session ID

```pulse
fn alloc_sid (_:unit)
  requires emp
  returns _:sid_ref_t
  ensures emp
{
  let sid_ref = alloc #nat 0;
  let lk = L.new_lock (exists_ (fun n -> R.pts_to sid_ref n));
  ((| sid_ref, lk |) <: sid_ref_t)
}
```
let sid_ref : sid_ref_t = run_stt(alloc_sid ())


(* ----------- IMPLEMENTATION ----------- *)

(*
  OpenSession: Part of DPE API 
  Create a context table and context table lock for the new session. 
  Add the context table lock to the session table. 
  NOTE: Current implementation disregards session protocol 
*)
```pulse
fn open_session (_:unit)
  requires emp
  ensures emp
{
  let cht = alloc_ht #cht_sig cht_len;

  let sht = dfst locked_sht;
  let sht_lk = dsnd locked_sht;
  let sid_lk = dsnd sid_ref;

  L.acquire #(exists_ (fun n -> R.pts_to (dfst sid_ref) n)) sid_lk;
  L.acquire #(ht_perm sht_sig sht) sht_lk;

  let sid = !(dfst sid_ref);

  unfold (ht_perm sht_sig sht);
  with pht. assert (models sht_sig sht pht);

  let b = not_full #sht_sig #pht sht;

  if b {
    PHT.insert #sht_sig #pht sht sid cht;
    dfst sid_ref := sid + 1;

    fold (ht_perm sht_sig sht);
    L.release #(exists_ (fun n -> R.pts_to (dfst sid_ref) n)) sid_lk;
    L.release #(ht_perm sht_sig sht) sht_lk;
  } else {
    // ERROR -- table full
    fold (ht_perm sht_sig sht);
    L.release #(exists_ (fun n -> R.pts_to (dfst sid_ref) n)) sid_lk;
    L.release #(ht_perm sht_sig sht) sht_lk;
  }
}
```

(*
  DestroyContext: Part of DPE API 
  Destroy the context pointed to by the handle by freeing the
  arrays in the context (zeroize the UDS, if applicable).
  NOTE: Current implementation disregards session protocol 
*)
```pulse
fn destroy_context (sid:nat) (ctxt_hndl:nat)
  requires emp
  ensures emp
{
  let sht = dfst locked_sht;
  let sht_lk = dsnd locked_sht;
  L.acquire #(ht_perm sht_sig sht) sht_lk;

  unfold (ht_perm sht_sig sht);
  with spht. assert (models sht_sig sht spht);

  let opt_locked_cht = PHT.lookup #sht_sig #spht sht sid;

  match opt_locked_cht {
  Some locked_cht -> {
    let cht = dfst locked_cht;
    let cht_lk = dsnd locked_cht;
    L.acquire #(ht_perm cht_sig cht) cht_lk;

    unfold (ht_perm cht_sig cht);
    with cpht0. assert (models cht_sig cht cpht0);

    let opt_locked_ctxt = PHT.lookup #cht_sig #cpht0 cht ctxt_hndl;
    match opt_locked_ctxt {
    Some locked_ctxt -> {
      let ctxt = dfst locked_ctxt;
      let ctxt_lk = dsnd locked_ctxt;
      L.acquire #(context_perm ctxt) ctxt_lk;
      match ctxt {
        Engine_context c -> {
          rewrite (context_perm ctxt) as (engine_context_perm c);
          unfold (engine_context_perm c);
          A.zeroize uds_len c.uds #uds_bytes;
          disable_uds ();
          A.free c.uds;
          fold (ht_perm cht_sig cht);
          fold (ht_perm sht_sig sht);
          L.release #(ht_perm cht_sig cht) cht_lk;
          L.release #(ht_perm sht_sig sht) sht_lk;
        }
        L0_context c -> {
          rewrite (context_perm ctxt) as (l0_context_perm c);
          unfold (l0_context_perm c);
          A.free c.cdi;
          fold (ht_perm cht_sig cht);
          fold (ht_perm sht_sig sht);
          L.release #(ht_perm cht_sig cht) cht_lk;
          L.release #(ht_perm sht_sig sht) sht_lk;
        }
        L1_context c -> {
          rewrite (context_perm ctxt) as (l1_context_perm c);
          unfold (l1_context_perm c);
          A.free c.deviceID_priv;
          A.free c.deviceID_pub;
          A.free c.aliasKey_priv;
          A.free c.aliasKey_pub;
          A.free c.aliasKeyCRT;
          A.free c.deviceIDCSR;
          fold (ht_perm cht_sig cht);
          fold (ht_perm sht_sig sht);
          L.release #(ht_perm cht_sig cht) cht_lk;
          L.release #(ht_perm sht_sig sht) sht_lk;
      }}}
    None -> {
      // ERROR - bad context handle
      fold (ht_perm cht_sig cht);
      fold (ht_perm sht_sig sht);
      L.release #(ht_perm cht_sig cht) cht_lk;
      L.release #(ht_perm sht_sig sht) sht_lk;
    }}}
  None -> {
    // ERROR - bad session ID
    fold (ht_perm sht_sig sht);
    L.release #(ht_perm sht_sig sht) sht_lk;
  }}
}
```

```pulse
fn destroy_cht (ht:ht_t cht_sig)
  requires ht_perm cht_sig ht
  ensures emp
{
  let mut off = 0sz;

  unfold (ht_perm cht_sig ht);
  with pht. assert (models cht_sig ht pht);
  unfold (models cht_sig ht pht);

  while (let voff = !off; (voff < ht.sz))
  invariant b. exists (voff:US.t). (
    A.pts_to ht.contents pht.repr **
    R.pts_to off voff **
    pure (
      US.v ht.sz == pht.sz /\
      voff <= ht.sz /\
      b == (voff < ht.sz)
    )
  )
  {
    let voff = !off;
    let c = (ht.contents).(voff);
    match c {
      Used k v -> {
      let ctxt = dfst v;
      let ctxt_lk = dsnd v;
      L.acquire #(context_perm ctxt) ctxt_lk;
      match ctxt {
        Engine_context c -> {
          rewrite (context_perm ctxt) as (engine_context_perm c);
          unfold (engine_context_perm c);
          A.zeroize uds_len c.uds #uds_bytes;
          disable_uds ();
          A.free c.uds;
        }
        L0_context c -> {
          rewrite (context_perm ctxt) as (l0_context_perm c);
          unfold (l0_context_perm c);
          A.free c.cdi;
        }
        L1_context c -> {
          rewrite (context_perm ctxt) as (l1_context_perm c);
          unfold (l1_context_perm c);
          A.free c.deviceID_priv;
          A.free c.deviceID_pub;
          A.free c.aliasKey_priv;
          A.free c.aliasKey_pub;
          A.free c.aliasKeyCRT;
          A.free c.deviceIDCSR;
        }
      }}
      _ -> {
        off := voff + 1sz;
      }
    }
  };
  A.free ht.contents;
}
```

(* 
  CloseSession: Part of DPE API 
  Destroy the context table for the session and remove the reference
  to it from the session table. 
  NOTE: Current implementation disregards session protocol 
*)
```pulse
fn close_session (sid:nat)
  requires emp
  ensures emp
{
  let sht = dfst locked_sht;
  let sht_lk = dsnd locked_sht;
  L.acquire #(ht_perm sht_sig sht) sht_lk;

  unfold (ht_perm sht_sig sht);
  with pht. assert (models sht_sig sht pht);

  let opt_locked_cht = PHT.lookup #sht_sig #pht sht sid;

  match opt_locked_cht {
  Some locked_cht -> { 
    let cht = dfst locked_cht;
    let cht_lk = dsnd locked_cht;
    // Note: We don't release this lock because we give up permission
    // on the cht when we free its entries by calling destroy_cht
    L.acquire #(ht_perm cht_sig cht) cht_lk;
    destroy_cht cht;
    PHT.delete #sht_sig #pht sht sid;
    fold (ht_perm sht_sig sht);
    L.release #(ht_perm sht_sig sht) sht_lk;
  }
  None -> {
    // ERROR -- bad session ID
    fold (ht_perm sht_sig sht);
    L.release #(ht_perm sht_sig sht) sht_lk;
  }}
}
```

// TODO: 
let prng (_:unit) : nat = admit()

```pulse
fn init_engine_ctxt (uds:A.larray U8.t (US.v uds_len))
  requires (
    A.pts_to uds uds_bytes **
    uds_is_enabled **
    pure (A.is_full_array uds)
  )
  returns _:locked_context_t
  ensures A.pts_to uds uds_bytes
{
  let uds_buf = A.alloc 0uy uds_len;
  memcpy uds_len uds uds_buf;
  let engine_context = mk_engine_context uds_buf;

  rewrite (A.pts_to uds_buf uds_bytes) 
    as (A.pts_to engine_context.uds uds_bytes);
  fold (engine_context_perm engine_context);

  let ctxt = mk_engine_context_t engine_context;

  rewrite (engine_context_perm engine_context) as (context_perm ctxt);

  let ctxt_lk = L.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```

```pulse
fn _init_l0_ctxt (cdi:A.larray U8.t (US.v dice_digest_len)) (#s:erased (elseq U8.t dice_digest_len))
  requires 
    A.pts_to cdi s **
    pure (A.is_full_array cdi)
  returns _:locked_context_t
  ensures 
    A.pts_to cdi s
{
  let cdi_buf = A.alloc 0uy dice_digest_len;
  memcpy dice_digest_len cdi cdi_buf;
  let l0_context = mk_l0_context cdi_buf;
  rewrite (A.pts_to cdi_buf s)
    as (A.pts_to l0_context.cdi s);
  fold (l0_context_perm l0_context);
  let ctxt = mk_l0_context_t l0_context;
  rewrite (l0_context_perm l0_context) as (context_perm ctxt);
  let ctxt_lk = L.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```
let init_l0_ctxt cdi #s = _init_l0_ctxt cdi #s

assume val coerce_seq_create (l:US.t) (s:(Seq.seq U8.t){s == Seq.create (US.v l) 0uy}) : elseq U8.t l

```pulse
fn _init_l1_ctxt (deviceIDCSR_len: US.t) (aliasKeyCRT_len: US.t) 
                (deviceID_priv: A.larray U8.t (US.v v32us)) (deviceID_pub: A.larray U8.t (US.v v32us))
                (aliasKey_priv: A.larray U8.t (US.v v32us)) (aliasKey_pub: A.larray U8.t (US.v v32us)) 
                (deviceIDCSR: A.larray U8.t (US.v deviceIDCSR_len)) (aliasKeyCRT: A.larray U8.t (US.v aliasKeyCRT_len))
                (#s1 #s2 #s3 #s4: erased (elseq U8.t v32us)) 
                (#s5:erased (elseq U8.t deviceIDCSR_len))
                (#s6:erased (elseq U8.t aliasKeyCRT_len))
  requires A.pts_to deviceID_priv s1 ** 
           A.pts_to deviceID_pub s2 ** 
           A.pts_to aliasKey_priv s3 ** 
           A.pts_to aliasKey_pub s4 ** 
           A.pts_to deviceIDCSR s5 **
           A.pts_to aliasKeyCRT s6
  returns _:locked_context_t
  ensures 
    A.pts_to deviceID_priv s1 ** 
    A.pts_to deviceID_pub s2 **
    A.pts_to aliasKey_priv s3 ** 
    A.pts_to aliasKey_pub s4 ** 
    A.pts_to deviceIDCSR s5 **
    A.pts_to aliasKeyCRT s6
{
  let deviceID_pub_buf = A.alloc 0uy v32us;
  let deviceID_priv_buf = A.alloc 0uy v32us;
  let aliasKey_priv_buf = A.alloc 0uy v32us;
  let aliasKey_pub_buf = A.alloc 0uy v32us;
  let deviceIDCSR_buf = A.alloc 0uy deviceIDCSR_len;
  let aliasKeyCRT_buf = A.alloc 0uy aliasKeyCRT_len;
  memcpy v32us deviceID_priv deviceID_priv_buf;
  memcpy v32us deviceID_pub deviceID_pub_buf;
  memcpy v32us aliasKey_priv aliasKey_priv_buf;
  memcpy v32us aliasKey_pub aliasKey_pub_buf;
  memcpy deviceIDCSR_len deviceIDCSR deviceIDCSR_buf;
  memcpy aliasKeyCRT_len aliasKeyCRT aliasKeyCRT_buf;

  let l1_context = mk_l1_context deviceID_priv_buf deviceID_pub_buf aliasKey_priv_buf aliasKey_pub_buf aliasKeyCRT_buf deviceIDCSR_buf;
  rewrite (A.pts_to deviceID_priv_buf s1 **
           A.pts_to deviceID_pub_buf s2 **
           A.pts_to aliasKey_priv_buf s3 **
           A.pts_to aliasKey_pub_buf s4 **
           A.pts_to deviceIDCSR_buf s5 **
           A.pts_to aliasKeyCRT_buf s6)
       as (A.pts_to l1_context.deviceID_priv s1**
           A.pts_to l1_context.deviceID_pub s2 **
           A.pts_to l1_context.aliasKey_priv s3 **
           A.pts_to l1_context.aliasKey_pub s4 **
           A.pts_to l1_context.deviceIDCSR s5 **
           A.pts_to l1_context.aliasKeyCRT s6);
  fold (l1_context_perm l1_context);
  let ctxt = mk_l1_context_t l1_context;
  rewrite (l1_context_perm l1_context) as (context_perm ctxt);
  let ctxt_lk = L.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```
let init_l1_ctxt deviceIDCSR_len aliasKeyCRT_len deviceID_priv deviceID_pub
  aliasKey_priv aliasKey_pub deviceIDCSR aliasKeyCRT #s1 #s2 #s3 #s4 #s5 #s6
  = _init_l1_ctxt deviceIDCSR_len aliasKeyCRT_len deviceID_priv deviceID_pub
    aliasKey_priv aliasKey_pub deviceIDCSR aliasKeyCRT #s1 #s2 #s3 #s4 #s5 #s6
(*
  InitializeContext: Part of DPE API 
  Create a context in the initial state (engine context) and store the context
  in the current session's context table. 
*)
```pulse
fn initialize_context (sid:nat) (uds:A.larray U8.t (US.v uds_len))
  requires (
    A.pts_to uds uds_bytes ** 
    uds_is_enabled **
    pure (A.is_full_array uds)
  )
  returns _:nat
  ensures A.pts_to uds uds_bytes
{
  let locked_context = init_engine_ctxt uds;
  let ctxt_hndl = prng ();

  let sht = dfst locked_sht;
  let sht_lk = dsnd locked_sht;
  L.acquire #(ht_perm sht_sig sht) sht_lk;

  unfold (ht_perm sht_sig sht);
  with spht. assert (models sht_sig sht spht);

  let opt_locked_cht = PHT.lookup #sht_sig #spht sht sid;

  match opt_locked_cht {
  Some locked_cht -> {
    let cht = dfst locked_cht;
    let cht_lk = dsnd locked_cht;
    L.acquire #(ht_perm cht_sig cht) cht_lk;

    unfold (ht_perm cht_sig cht);
    with cpht. assert (models cht_sig cht cpht);
    let b = not_full #cht_sig #cpht cht;

    if b {
      PHT.insert #cht_sig #cpht cht ctxt_hndl locked_context;

      fold (ht_perm sht_sig sht);
      fold (ht_perm cht_sig cht);
      L.release #(ht_perm sht_sig sht) sht_lk;
      L.release #(ht_perm cht_sig cht) cht_lk;
      
      ctxt_hndl
    } else {
      // ERROR -- table full
      fold (ht_perm sht_sig sht);
      fold (ht_perm cht_sig cht);
      L.release #(ht_perm sht_sig sht) sht_lk;
      L.release #(ht_perm cht_sig cht) cht_lk;
      
      ctxt_hndl 
    }}
  None -> {
    // ERROR -- bad session ID
    fold (ht_perm sht_sig sht);
    L.release #(ht_perm sht_sig sht) sht_lk;
    0
  }}
}
```


