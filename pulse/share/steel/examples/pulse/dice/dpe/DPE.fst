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
open L0Types
open EngineCore
open L0Core
open Pulse.Class.BoundedIntegers

friend Pulse.Steel.Wrapper

(* L1 Context -- no dedicated L1 logic, so there's no good place for this to live *)

noeq
type l1_context = { deviceID_priv: A.larray U8.t (US.v v32us);
                    deviceID_pub: A.larray U8.t (US.v v32us);
                    aliasKey_priv: A.larray U8.t (US.v v32us);
                    aliasKey_pub: A.larray U8.t (US.v v32us);
                    aliasKeyCRT: A.array U8.t;
                    deviceIDCSR: A.array U8.t; }

let l1_context_perm (c:l1_context)
  : vprop
  = exists_ (fun s -> A.pts_to c.deviceID_priv full_perm s) `star`
    exists_ (fun s -> A.pts_to c.deviceID_pub full_perm s) `star`
    exists_ (fun s -> A.pts_to c.aliasKey_priv full_perm s) `star`
    exists_ (fun s -> A.pts_to c.aliasKey_pub full_perm s) `star`
    exists_ (fun s -> A.pts_to c.aliasKeyCRT full_perm s) `star`
    exists_ (fun s -> A.pts_to c.deviceIDCSR full_perm s) `star`
    pure (
      A.is_full_array c.deviceID_priv /\
      A.is_full_array c.deviceID_pub /\
      A.is_full_array c.aliasKey_priv /\
      A.is_full_array c.aliasKey_pub /\
      A.is_full_array c.aliasKeyCRT /\
      A.is_full_array c.deviceIDCSR
    )

let mk_l1_context deviceID_priv deviceID_pub aliasKey_priv aliasKey_pub aliasKeyCRT deviceIDCSR 
  = { deviceID_priv; deviceID_pub; aliasKey_priv; aliasKey_pub; aliasKeyCRT; deviceIDCSR }

(* Context *)
noeq
type context_t = 
  | Engine_context : c:engine_context -> context_t
  | L0_context     : c:l0_context -> context_t
  | L1_context     : c:l1_context -> context_t

let context_perm (t:context_t) : vprop = 
  match t with
  | Engine_context c -> engine_context_perm c
  | L0_context c -> l0_context_perm c
  | L1_context c -> l1_context_perm c

let mk_engine_context_t engine_context = Engine_context engine_context
let mk_l0_context_t l0_context = L0_context l0_context
let mk_l1_context_t l1_context = L1_context l1_context

let locked_context_t = c:context_t & L.lock (context_perm c)


(* Record *)
noeq
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t

noeq
type repr_t = 
  | Engine_repr : r:engine_record_repr -> repr_t
  | L0_repr     : r:l0_record_repr -> repr_t

let record_perm (t_rec:record_t) (t_rep:repr_t) : vprop = 
  match t_rec with
  | Engine_record r -> (
    match t_rep with 
    | Engine_repr r0 -> engine_record_perm r r0
    | _ -> pure(false)
  )
  | L0_record r -> (
    match t_rep with
    | L0_repr r0 -> l0_record_perm r r0
    | _ -> pure(false)
  )

(* ----------- GLOBAL STATE ----------- *)

type sid_ref_t = r:R.ref nat & L.lock (exists_ (fun n -> R.pts_to r full_perm n))
assume val get (#s:pht_sig_us) (ht:ht_t s) (k:s.keyt) : s.valt

assume val dpe_hashf : nat -> US.t
assume val sht_len : pos_us
assume val cht_len : pos_us
let cht_sig : pht_sig_us = mk_pht_sig_us nat locked_context_t dpe_hashf
let sht_sig : pht_sig_us = mk_pht_sig_us nat (locked_ht_t cht_sig) dpe_hashf 

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
assume val prng (_:unit) : nat

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
fn init_l0_ctxt (cdi:A.larray U8.t (US.v dice_digest_len))
  requires exists (s:elseq U8.t dice_digest_len). 
    A.pts_to cdi full_perm s **
    pure (A.is_full_array cdi)
  returns _:locked_context_t
  ensures exists (s:elseq U8.t dice_digest_len). 
    A.pts_to cdi full_perm s
{
  let cdi_buf = new_array 0uy dice_digest_len;
  memcpy dice_digest_len cdi cdi_buf;
  let l0_context = mk_l0_context cdi_buf;
// FIXME: pulse can't prove equality in the following two rewrites 
// has something to do with not unwrapping the existential
  // rewrite (exists_ (fun s -> A.pts_to cdi_buf full_perm s)) 
  //   as (exists_ (fun s -> A.pts_to l0_context.cdi full_perm s)); 
  drop_ (exists_ (fun (s:elseq U8.t dice_digest_len) -> A.pts_to cdi_buf full_perm s));
  assume_ (exists_ (fun (s:elseq U8.t dice_digest_len) -> A.pts_to l0_context.cdi full_perm s));
  fold (l0_context_perm l0_context);
  let ctxt = mk_l0_context_t l0_context;
  rewrite (l0_context_perm l0_context) as (context_perm ctxt);
  let ctxt_lk = W.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```

assume val coerce_seq_create (l:US.t) (s:(Seq.seq U8.t){s == Seq.create (US.v l) 0uy}) : elseq U8.t l

```pulse
fn init_l1_ctxt (deviceIDCSR_len: US.t) (aliasKeyCRT_len: US.t) 
                (deviceID_priv: A.larray U8.t (US.v v32us)) (deviceID_pub: A.larray U8.t (US.v v32us))
                (aliasKey_priv: A.larray U8.t (US.v v32us)) (aliasKey_pub: A.larray U8.t (US.v v32us)) 
                (deviceIDCSR: A.larray U8.t (US.v deviceIDCSR_len)) (aliasKeyCRT: A.larray U8.t (US.v aliasKeyCRT_len))
  requires exists (s1:elseq U8.t v32us). A.pts_to deviceID_priv full_perm s1 ** 
           exists (s2:elseq U8.t v32us). A.pts_to deviceID_pub full_perm s2 ** 
           exists (s3:elseq U8.t v32us). A.pts_to aliasKey_priv full_perm s3 ** 
           exists (s4:elseq U8.t v32us). A.pts_to aliasKey_pub full_perm s4 ** 
           exists (s5:erased (elseq U8.t deviceIDCSR_len)). A.pts_to deviceIDCSR full_perm s5 **
           exists (s6:erased (elseq U8.t aliasKeyCRT_len)). A.pts_to aliasKeyCRT full_perm s6
  returns _:locked_context_t
  ensures 
    exists s. A.pts_to deviceID_priv full_perm s ** 
    exists s. A.pts_to deviceID_pub full_perm s **
    exists s. A.pts_to aliasKey_priv full_perm s ** 
    exists s. A.pts_to aliasKey_pub full_perm s ** 
    exists s. A.pts_to deviceIDCSR full_perm s **
    exists s. A.pts_to aliasKeyCRT full_perm s
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
// FIXME: pulse can't prove equality in the following two rewrites 
// has something to do with not unwrapping the existential
  // rewrite (exists_ (fun s -> A.pts_to deviceID_priv_buf full_perm s) `star`
  //        exists_ (fun s -> A.pts_to deviceID_pub_buf full_perm s) `star`
  //        exists_ (fun s -> A.pts_to aliasKey_priv_buf full_perm s) `star`
  //        exists_ (fun s -> A.pts_to aliasKey_pub_buf full_perm s) `star`
  //        exists_ (fun s -> A.pts_to aliasKeyCRT_buf full_perm s) `star`
  //        exists_ (fun s -> A.pts_to deviceIDCSR_buf full_perm s))
  //   as (exists_ (fun s -> A.pts_to l1_context.deviceID_priv full_perm s) `star`
  //       exists_ (fun s -> A.pts_to l1_context.deviceID_pub full_perm s) `star`
  //       exists_ (fun s -> A.pts_to l1_context.aliasKey_priv full_perm s) `star`
  //       exists_ (fun s -> A.pts_to l1_context.aliasKey_pub full_perm s) `star`
  //       exists_ (fun s -> A.pts_to l1_context.aliasKeyCRT full_perm s) `star`
  //       exists_ (fun s -> A.pts_to l1_context.deviceIDCSR full_perm s));
  drop_ (exists_ (fun s -> A.pts_to deviceID_priv_buf full_perm s) `star`
         exists_ (fun s -> A.pts_to deviceID_pub_buf full_perm s) `star`
         exists_ (fun s -> A.pts_to aliasKey_priv_buf full_perm s) `star`
         exists_ (fun s -> A.pts_to aliasKey_pub_buf full_perm s) `star`
         exists_ (fun s -> A.pts_to aliasKeyCRT_buf full_perm s) `star`
         exists_ (fun s -> A.pts_to deviceIDCSR_buf full_perm s));
  assume_ (exists_ (fun s -> A.pts_to l1_context.deviceID_priv full_perm s) `star`
           exists_ (fun s -> A.pts_to l1_context.deviceID_pub full_perm s) `star`
           exists_ (fun s -> A.pts_to l1_context.aliasKey_priv full_perm s) `star`
           exists_ (fun s -> A.pts_to l1_context.aliasKey_pub full_perm s) `star`
           exists_ (fun s -> A.pts_to l1_context.aliasKeyCRT full_perm s) `star`
           exists_ (fun s -> A.pts_to l1_context.deviceIDCSR full_perm s));
  fold (l1_context_perm l1_context);
  let ctxt = mk_l1_context_t l1_context;
  rewrite (l1_context_perm l1_context) as (context_perm ctxt);
  let ctxt_lk = W.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```

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

(*
  DeriveChild: Part of DPE API 
  Execute the DICE layer associated with the current context and produce a 
  new context. Destroy the current context in the current session's context table 
  and store the new context in the table.
  NOTE: Returns 0 if called when ctxt has type L1_context (bad invocation)
*)
```pulse
fn derive_child (sid:nat) (ctxt_hndl:nat) (record:record_t) (repr:repr_t)
  requires record_perm record repr
  returns _:nat
  ensures record_perm record repr
{
  let new_ctxt_hndl = prng ();

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
      // NOTE: we won't eventually release engine_context_perm because we won't 
      // own it anymore -- we will disable the uds and free the uds array
      rewrite (context_perm ctxt) as (engine_context_perm c);
      unfold (engine_context_perm c);

      match record {
      Engine_record r -> {
        match repr {
        Engine_repr r0 -> {       
          rewrite (record_perm record repr) as (engine_record_perm r r0); 

          let cdi = new_array 0uy dice_digest_len;
          EngineCore.engine_main cdi c.uds r; // FIXME: match on dice return type
          free_array c.uds;

          let new_locked_context = init_l0_ctxt cdi;
          with s. assert (A.pts_to cdi full_perm s);
          free_array cdi #(coerce dice_digest_len s);
          
          PHT.delete #cht_sig #cpht0 cht ctxt_hndl;
          with cpht1. assert (models cht_sig cht cpht1);
          let b = not_full #cht_sig #cpht1 cht;

          if b {
            PHT.insert #cht_sig #cpht1 cht new_ctxt_hndl new_locked_context; 

            rewrite (engine_record_perm r r0) as (record_perm record repr);

            fold (ht_perm sht_sig sht);
            fold (ht_perm cht_sig cht);
            W.release #(ht_perm sht_sig sht) sht_lk;
            W.release #(ht_perm cht_sig cht) cht_lk;

            new_ctxt_hndl
          } else {
            // ERROR -- table full
            rewrite (engine_record_perm r r0) as (record_perm record repr);

            fold (ht_perm sht_sig sht);
            fold (ht_perm cht_sig cht);
            W.release #(ht_perm sht_sig sht) sht_lk;
            W.release #(ht_perm cht_sig cht) cht_lk;

            new_ctxt_hndl
          }
        }
        _ -> {
          // ERROR - repr should have type (Egnine_repr r0)
          zeroize_array uds_len c.uds #uds_bytes;
          disable_uds ();
          free_array c.uds;

          fold (ht_perm sht_sig sht);
          fold (ht_perm cht_sig cht);
          W.release #(ht_perm sht_sig sht) sht_lk;
          W.release #(ht_perm cht_sig cht) cht_lk;
          0
        }}
      }
      _ -> {
        // ERROR - record should have type (Engine_record r)
        zeroize_array uds_len c.uds;
        disable_uds ();
        free_array c.uds;

        fold (ht_perm sht_sig sht);
        fold (ht_perm cht_sig cht);
        W.release #(ht_perm sht_sig sht) sht_lk;
        W.release #(ht_perm cht_sig cht) cht_lk;
        0
      }}
    }
    L0_context c -> {    
      // NOTE: we won't eventually release l0_context_perm because we won't 
      // own it anymore -- we will free the cdi array
      rewrite (context_perm ctxt) as (l0_context_perm c);
      unfold (l0_context_perm c);

      with s. assert (A.pts_to c.cdi full_perm s);

      match record {
      L0_record r -> {
        match repr {
        L0_repr r0 -> {
          let idcsr_ing = r.deviceIDCSR_ingredients;
          let akcrt_ing = r.aliasKeyCRT_ingredients;

          let deviceIDCRI_len = len_of_deviceIDCRI  idcsr_ing.version idcsr_ing.s_common 
                                                    idcsr_ing.s_org idcsr_ing.s_country;
          let aliasKeyTBS_len = len_of_aliasKeyTBS  akcrt_ing.serialNumber akcrt_ing.i_common 
                                                    akcrt_ing.i_org akcrt_ing.i_country 
                                                    akcrt_ing.s_common akcrt_ing.s_org 
                                                    akcrt_ing.s_country akcrt_ing.l0_version;
          let deviceIDCSR_len = length_of_deviceIDCSR deviceIDCRI_len;
          let aliasKeyCRT_len = length_of_aliasKeyCRT aliasKeyTBS_len;

          let deviceID_pub = new_array 0uy v32us;
          let deviceID_priv = new_array 0uy v32us;
          let aliasKey_pub = new_array 0uy v32us;
          let aliasKey_priv = new_array 0uy v32us;
          let deviceIDCSR = new_array 0uy deviceIDCSR_len;
          let aliasKeyCRT = new_array 0uy aliasKeyCRT_len;

          rewrite (record_perm record repr) as (l0_record_perm r r0); 

          assume_ (pure(valid_hkdf_ikm_len (digest_len dice_hash_alg)));
          
          L0Core.l0_main  c.cdi deviceID_pub deviceID_priv 
                          aliasKey_pub aliasKey_priv 
                          aliasKeyTBS_len aliasKeyCRT_len aliasKeyCRT 
                          deviceIDCRI_len deviceIDCSR_len deviceIDCSR r;
          free_array c.cdi;

          with (s1:elseq U8.t v32us). assert (A.pts_to aliasKey_priv full_perm s1);
          let new_locked_context = init_l1_ctxt deviceIDCSR_len aliasKeyCRT_len 
                                                deviceID_priv deviceID_pub
                                                aliasKey_priv aliasKey_pub 
                                                deviceIDCSR aliasKeyCRT;
          free_array deviceID_pub;
          free_array deviceID_priv;
          free_array aliasKey_pub;
          free_array aliasKey_priv;
          free_array deviceIDCSR;
          free_array aliasKeyCRT;
          
          PHT.delete #cht_sig #cpht0 cht ctxt_hndl;
          with cpht1. assert (models cht_sig cht cpht1);
          let b = not_full #cht_sig #cpht1 cht;

          if b {
            PHT.insert #cht_sig #cpht1 cht new_ctxt_hndl new_locked_context;

            rewrite (l0_record_perm r r0) as (record_perm record repr);

            fold (ht_perm sht_sig sht);
            fold (ht_perm cht_sig cht);
            W.release #(ht_perm sht_sig sht) sht_lk;
            W.release #(ht_perm cht_sig cht) cht_lk;

            new_ctxt_hndl
          } else {
            // ERROR -- table full
            rewrite (l0_record_perm r r0) as (record_perm record repr);

            fold (ht_perm sht_sig sht);
            fold (ht_perm cht_sig cht);
            W.release #(ht_perm sht_sig sht) sht_lk;
            W.release #(ht_perm cht_sig cht) cht_lk;

            new_ctxt_hndl
          }
        }
        _ -> {
          // ERROR - repr should have type (L0_repr r0)
          zeroize_array dice_digest_len c.cdi;
          free_array c.cdi;

          fold (ht_perm sht_sig sht);
          fold (ht_perm cht_sig cht);
          W.release #(ht_perm sht_sig sht) sht_lk;
          W.release #(ht_perm cht_sig cht) cht_lk;
          0
        }}
      }
      _ -> {
        // ERROR - record should have type (L0_record r)
        zeroize_array dice_digest_len c.cdi;
        free_array c.cdi;

        fold (ht_perm sht_sig sht);
        fold (ht_perm cht_sig cht);
        W.release #(ht_perm sht_sig sht) sht_lk;
        W.release #(ht_perm cht_sig cht) cht_lk;
        0
      }}
    }
    _ -> { 
      // ERROR - bad invocation of DeriveChild
      fold (ht_perm sht_sig sht);
      fold (ht_perm cht_sig cht);
      W.release #(context_perm ctxt) ctxt_lk;
      W.release #(ht_perm sht_sig sht) sht_lk;
      W.release #(ht_perm cht_sig cht) cht_lk;
      0
    }}}
    None -> { 
    // ERROR -- cannot invoke DeriveChild with L1 context
    fold (ht_perm sht_sig sht);
    fold (ht_perm cht_sig cht);
    W.release #(ht_perm sht_sig sht) sht_lk;
    W.release #(ht_perm cht_sig cht) cht_lk;
    0
    }}}
  None -> { 
  // ERROR - bad session ID
  fold (ht_perm sht_sig sht);
  W.release #(ht_perm sht_sig sht) sht_lk;
  0
  }}
}
```
