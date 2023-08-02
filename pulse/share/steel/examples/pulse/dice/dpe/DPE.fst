module DPE
open Pulse.Main
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
open Pulse.Steel.Wrapper
module W = Pulse.Steel.Wrapper
module L = Steel.ST.SpinLock
module A = Steel.ST.Array
module R = Steel.ST.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open Array
open LinearScanHashTable
open PulseHashTable
module PHT = PulseHashTable
module LSHT = LinearScanHashTable
open HACL
open X509
open EngineTypes
open EngineCore
open L0Core
open L0Types
open Pulse.Class.BoundedIntegers

friend Pulse.Steel.Wrapper


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
  let contents = new_array #(cell s.keyt s.valt) Clean l;
  let ht = mk_ht l contents;
  let pht = mk_init_pht #s l;
  rewrite (A.pts_to contents full_perm (Seq.create (US.v l) Clean))
    as (A.pts_to ht.contents full_perm pht.repr);
  fold (models s ht pht);
  fold (ht_perm s ht);
  let lk = W.new_lock (ht_perm s ht);
  ((| ht, lk |) <: locked_ht_t s)
}
```
let locked_sht : locked_ht_t sht_sig = alloc_ht #sht_sig sht_len ()

// A number that tracks the next session ID

```pulse
fn alloc_sid (_:unit)
  requires emp
  returns _:sid_ref_t
  ensures emp
{
  let sid_ref = W.alloc #nat 0;
  let lk = W.new_lock (exists_ (fun n -> R.pts_to sid_ref full_perm n));
  ((| sid_ref, lk |) <: sid_ref_t)
}
```
let sid_ref : sid_ref_t = alloc_sid () ()


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

  W.acquire #(exists_ (fun n -> R.pts_to (dfst sid_ref) full_perm n)) sid_lk;
  W.acquire #(ht_perm sht_sig sht) sht_lk;

  let sid = !(dfst sid_ref);

  unfold (ht_perm sht_sig sht);
  with pht. assert (models sht_sig sht pht);

  let b = not_full #sht_sig #pht sht;

  if b {
    PHT.insert #sht_sig #pht sht sid cht;
    dfst sid_ref := sid + 1;

    fold (ht_perm sht_sig sht);
    W.release #(exists_ (fun n -> R.pts_to (dfst sid_ref) full_perm n)) sid_lk;
    W.release #(ht_perm sht_sig sht) sht_lk;
  } else {
    // ERROR -- table full
    fold (ht_perm sht_sig sht);
    W.release #(exists_ (fun n -> R.pts_to (dfst sid_ref) full_perm n)) sid_lk;
    W.release #(ht_perm sht_sig sht) sht_lk;
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
  W.acquire #(ht_perm sht_sig sht) sht_lk;

  unfold (ht_perm sht_sig sht);
  with spht. assert (models sht_sig sht spht);

  let opt_locked_cht = PHT.lookup #sht_sig #spht sht sid;

  match opt_locked_cht {
  Some locked_cht -> {
    let cht = dfst locked_cht;
    let cht_lk = dsnd locked_cht;
    W.acquire #(ht_perm cht_sig cht) cht_lk;

    unfold (ht_perm cht_sig cht);
    with cpht0. assert (models cht_sig cht cpht0);

    let opt_locked_ctxt = PHT.lookup #cht_sig #cpht0 cht ctxt_hndl;
    match opt_locked_ctxt {
    Some locked_ctxt -> {
      let ctxt = dfst locked_ctxt;
      let ctxt_lk = dsnd locked_ctxt;
      W.acquire #(context_perm ctxt) ctxt_lk;
      match ctxt {
        Engine_context c -> {
          rewrite (context_perm ctxt) as (engine_context_perm c);
          unfold (engine_context_perm c);
          zeroize_array uds_len c.uds #uds_bytes;
          disable_uds ();
          free_array c.uds;
          fold (ht_perm cht_sig cht);
          fold (ht_perm sht_sig sht);
          W.release #(ht_perm cht_sig cht) cht_lk;
          W.release #(ht_perm sht_sig sht) sht_lk;
        }
        L0_context c -> {
          rewrite (context_perm ctxt) as (l0_context_perm c);
          unfold (l0_context_perm c);
          free_array c.cdi;
          fold (ht_perm cht_sig cht);
          fold (ht_perm sht_sig sht);
          W.release #(ht_perm cht_sig cht) cht_lk;
          W.release #(ht_perm sht_sig sht) sht_lk;
        }
        L1_context c -> {
          rewrite (context_perm ctxt) as (l1_context_perm c);
          unfold (l1_context_perm c);
          free_array c.deviceID_priv;
          free_array c.deviceID_pub;
          free_array c.aliasKey_priv;
          free_array c.aliasKey_pub;
          free_array c.aliasKeyCRT;
          free_array c.deviceIDCSR;
          fold (ht_perm cht_sig cht);
          fold (ht_perm sht_sig sht);
          W.release #(ht_perm cht_sig cht) cht_lk;
          W.release #(ht_perm sht_sig sht) sht_lk;
      }}}
    None -> {
      // ERROR - bad context handle
      fold (ht_perm cht_sig cht);
      fold (ht_perm sht_sig sht);
      W.release #(ht_perm cht_sig cht) cht_lk;
      W.release #(ht_perm sht_sig sht) sht_lk;
    }}}
  None -> {
    // ERROR - bad session ID
    fold (ht_perm sht_sig sht);
    W.release #(ht_perm sht_sig sht) sht_lk;
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
    A.pts_to ht.contents full_perm pht.repr **
    R.pts_to off full_perm voff **
    pure (
      US.v ht.sz == pht.sz /\
      voff <= ht.sz /\
      b == (voff < ht.sz)
    )
  )
  {
    let voff = !off;
    let c = op_Array_Index ht.contents voff;
    match c {
      Used k v -> {
      let ctxt = dfst v;
      let ctxt_lk = dsnd v;
      W.acquire #(context_perm ctxt) ctxt_lk;
      match ctxt {
        Engine_context c -> {
          rewrite (context_perm ctxt) as (engine_context_perm c);
          unfold (engine_context_perm c);
          zeroize_array uds_len c.uds #uds_bytes;
          disable_uds ();
          free_array c.uds;
        }
        L0_context c -> {
          rewrite (context_perm ctxt) as (l0_context_perm c);
          unfold (l0_context_perm c);
          free_array c.cdi;
        }
        L1_context c -> {
          rewrite (context_perm ctxt) as (l1_context_perm c);
          unfold (l1_context_perm c);
          free_array c.deviceID_priv;
          free_array c.deviceID_pub;
          free_array c.aliasKey_priv;
          free_array c.aliasKey_pub;
          free_array c.aliasKeyCRT;
          free_array c.deviceIDCSR;
        }
      }}
      _ -> {
        off := voff + 1sz;
      }
    }
  };
  free_array ht.contents;
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
  W.acquire #(ht_perm sht_sig sht) sht_lk;

  unfold (ht_perm sht_sig sht);
  with pht. assert (models sht_sig sht pht);

  let opt_locked_cht = PHT.lookup #sht_sig #pht sht sid;

  match opt_locked_cht {
  Some locked_cht -> { 
    let cht = dfst locked_cht;
    let cht_lk = dsnd locked_cht;
    // Note: We don't release this lock because we give up permission
    // on the cht when we free its entries by calling destroy_cht
    W.acquire #(ht_perm cht_sig cht) cht_lk;
    destroy_cht cht;
    PHT.delete #sht_sig #pht sht sid;
    fold (ht_perm sht_sig sht);
    W.release #(ht_perm sht_sig sht) sht_lk;
  }
  None -> {
    // ERROR -- bad session ID
    fold (ht_perm sht_sig sht);
    W.release #(ht_perm sht_sig sht) sht_lk;
  }}
}
```

// TODO: 
let prng (_:unit) : nat = admit()

```pulse
fn init_engine_ctxt (uds:A.larray U8.t (US.v uds_len))
  requires (
    A.pts_to uds full_perm uds_bytes **
    uds_is_enabled **
    pure (A.is_full_array uds)
  )
  returns _:locked_context_t
  ensures A.pts_to uds full_perm uds_bytes
{
  let uds_buf = new_array 0uy uds_len;
  memcpy uds_len uds uds_buf;
  let engine_context = mk_engine_context uds_buf;

  rewrite (A.pts_to uds_buf full_perm uds_bytes) 
    as (A.pts_to engine_context.uds full_perm uds_bytes);
  fold (engine_context_perm engine_context);

  let ctxt = mk_engine_context_t engine_context;

  rewrite (engine_context_perm engine_context) as (context_perm ctxt);

  let ctxt_lk = W.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```

```pulse
fn _init_l0_ctxt (cdi:A.larray U8.t (US.v dice_digest_len)) (#s:erased (elseq U8.t dice_digest_len))
  requires 
    A.pts_to cdi full_perm s **
    pure (A.is_full_array cdi)
  returns _:locked_context_t
  ensures 
    A.pts_to cdi full_perm s
{
  let cdi_buf = new_array 0uy dice_digest_len;
  memcpy dice_digest_len cdi cdi_buf;
  let l0_context = mk_l0_context cdi_buf;
  rewrite (A.pts_to cdi_buf full_perm s)
    as (A.pts_to l0_context.cdi full_perm s);
  fold (l0_context_perm l0_context);
  let ctxt = mk_l0_context_t l0_context;
  rewrite (l0_context_perm l0_context) as (context_perm ctxt);
  let ctxt_lk = W.new_lock (context_perm ctxt);
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
  requires A.pts_to deviceID_priv full_perm s1 ** 
           A.pts_to deviceID_pub full_perm s2 ** 
           A.pts_to aliasKey_priv full_perm s3 ** 
           A.pts_to aliasKey_pub full_perm s4 ** 
           A.pts_to deviceIDCSR full_perm s5 **
           A.pts_to aliasKeyCRT full_perm s6
  returns _:locked_context_t
  ensures 
    A.pts_to deviceID_priv full_perm s1 ** 
    A.pts_to deviceID_pub full_perm s2 **
    A.pts_to aliasKey_priv full_perm s3 ** 
    A.pts_to aliasKey_pub full_perm s4 ** 
    A.pts_to deviceIDCSR full_perm s5 **
    A.pts_to aliasKeyCRT full_perm s6
{
  let deviceID_pub_buf = new_array 0uy v32us;
  let deviceID_priv_buf = new_array 0uy v32us;
  let aliasKey_priv_buf = new_array 0uy v32us;
  let aliasKey_pub_buf = new_array 0uy v32us;
  let deviceIDCSR_buf = new_array 0uy deviceIDCSR_len;
  let aliasKeyCRT_buf = new_array 0uy aliasKeyCRT_len;
  memcpy v32us deviceID_priv deviceID_priv_buf;
  memcpy v32us deviceID_pub deviceID_pub_buf;
  memcpy v32us aliasKey_priv aliasKey_priv_buf;
  memcpy v32us aliasKey_pub aliasKey_pub_buf;
  memcpy deviceIDCSR_len deviceIDCSR deviceIDCSR_buf;
  memcpy aliasKeyCRT_len aliasKeyCRT aliasKeyCRT_buf;

  let l1_context = mk_l1_context deviceID_priv_buf deviceID_pub_buf aliasKey_priv_buf aliasKey_pub_buf aliasKeyCRT_buf deviceIDCSR_buf;
  rewrite (A.pts_to deviceID_priv_buf full_perm s1 `star`
           A.pts_to deviceID_pub_buf full_perm s2 `star`
           A.pts_to aliasKey_priv_buf full_perm s3 `star`
           A.pts_to aliasKey_pub_buf full_perm s4 `star`
           A.pts_to deviceIDCSR_buf full_perm s5 `star`
           A.pts_to aliasKeyCRT_buf full_perm s6)
       as (A.pts_to l1_context.deviceID_priv full_perm s1`star`
           A.pts_to l1_context.deviceID_pub full_perm s2 `star`
           A.pts_to l1_context.aliasKey_priv full_perm s3 `star`
           A.pts_to l1_context.aliasKey_pub full_perm s4 `star`
           A.pts_to l1_context.deviceIDCSR full_perm s5 `star`
           A.pts_to l1_context.aliasKeyCRT full_perm s6);
  fold (l1_context_perm l1_context);
  let ctxt = mk_l1_context_t l1_context;
  rewrite (l1_context_perm l1_context) as (context_perm ctxt);
  let ctxt_lk = W.new_lock (context_perm ctxt);
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
    A.pts_to uds full_perm uds_bytes ** 
    uds_is_enabled **
    pure (A.is_full_array uds)
  )
  returns _:nat
  ensures A.pts_to uds full_perm uds_bytes
{
  let locked_context = init_engine_ctxt uds;
  let ctxt_hndl = prng ();

  let sht = dfst locked_sht;
  let sht_lk = dsnd locked_sht;
  W.acquire #(ht_perm sht_sig sht) sht_lk;

  unfold (ht_perm sht_sig sht);
  with spht. assert (models sht_sig sht spht);

  let opt_locked_cht = PHT.lookup #sht_sig #spht sht sid;

  match opt_locked_cht {
  Some locked_cht -> {
    let cht = dfst locked_cht;
    let cht_lk = dsnd locked_cht;
    W.acquire #(ht_perm cht_sig cht) cht_lk;

    unfold (ht_perm cht_sig cht);
    with cpht. assert (models cht_sig cht cpht);
    let b = not_full #cht_sig #cpht cht;

    if b {
      PHT.insert #cht_sig #cpht cht ctxt_hndl locked_context;

      fold (ht_perm sht_sig sht);
      fold (ht_perm cht_sig cht);
      W.release #(ht_perm sht_sig sht) sht_lk;
      W.release #(ht_perm cht_sig cht) cht_lk;
      
      ctxt_hndl
    } else {
      // ERROR -- table full
      fold (ht_perm sht_sig sht);
      fold (ht_perm cht_sig cht);
      W.release #(ht_perm sht_sig sht) sht_lk;
      W.release #(ht_perm cht_sig cht) cht_lk;
      
      ctxt_hndl 
    }}
  None -> {
    // ERROR -- bad session ID
    fold (ht_perm sht_sig sht);
    W.release #(ht_perm sht_sig sht) sht_lk;
    0
  }}
}
```


