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
module HT = Pulse.Lib.HashTable
module PHT = FStar.HashTable
open Pulse.Class.BoundedIntegers

assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a

(* Engine Context *)
noeq
type engine_context = { uds: A.larray U8.t (US.v uds_len); }

let engine_context_perm (c:engine_context) : vprop
  = A.pts_to c.uds full_perm uds_bytes ** 
    pure (A.is_full_array c.uds)

let mk_engine_context uds : engine_context = {uds}

(* L0 Context *)
noeq
type l0_context = { cdi: A.larray U8.t (US.v dice_digest_len); }

// FIXME: lost cdi_functional_correctness! 
let l0_context_perm (c:l0_context) : vprop
  = exists_ (fun (s:elseq U8.t dice_digest_len) -> A.pts_to c.cdi full_perm s) **
    pure (A.is_full_array c.cdi)

let mk_l0_context cdi : l0_context = {cdi}

(* L1 Context *)
noeq
type l1_context = { deviceID_priv: A.larray U8.t (US.v v32us);
                    deviceID_pub: A.larray U8.t (US.v v32us);
                    aliasKey_priv: A.larray U8.t (US.v v32us);
                    aliasKey_pub: A.larray U8.t (US.v v32us);
                    aliasKeyCRT: A.array U8.t;
                    deviceIDCSR: A.array U8.t; }

// FIXME: lost functoinal correctness! 
let l1_context_perm (c:l1_context)
  : vprop
  = exists_ (fun s -> A.pts_to c.deviceID_priv full_perm s) **
    exists_ (fun s -> A.pts_to c.deviceID_pub full_perm s) **
    exists_ (fun s -> A.pts_to c.aliasKey_priv full_perm s) **
    exists_ (fun s -> A.pts_to c.aliasKey_pub full_perm s) **
    exists_ (fun s -> A.pts_to c.aliasKeyCRT full_perm s) **
    exists_ (fun s -> A.pts_to c.deviceIDCSR full_perm s) **
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
  

(* Generic Context *)    // this is called an enumeration
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

// In the implmentation, we store contexts as values in a global hash table
// so we need a way to store and retrieve permission on the context. We do this
// by keeping a tuple of the context along with a lock on the context permission
let locked_context_t = c:context_t & L.lock (context_perm c)

let mk_engine_context_t engine_context = Engine_context engine_context
let mk_l0_context_t l0_context = L0_context l0_context
let mk_l1_context_t l1_context = L1_context l1_context

(* Record *)
noeq
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t

noeq
type repr_t = 
  | Engine_repr : r:engine_record_repr -> repr_t
  | L0_repr     : r:l0_record_repr -> repr_t

let record_perm (record:record_t) (repr:repr_t) : vprop = 
  match record with
  | Engine_record r -> (
    match repr with 
    | Engine_repr r0 -> engine_record_perm r r0
    | _ -> pure(false)
  )
  | L0_record r -> (
    match repr with
    | L0_repr r0 -> l0_record_perm r r0
    | _ -> pure(false)
  )

assume val get_engine_record_perm (record:record_t{Engine_record? record}) (repr:erased repr_t)
  : stt_ghost (erased engine_record_repr) emp_inames
              (record_perm record repr)
              (fun r0 -> engine_record_perm (Engine_record?.r record) r0 
                      ** pure(reveal repr == Engine_repr r0))
// ```pulse
// ghost fn get_engine_record_perm (record:(r:record_t{Engine_record? r})) (repr:erased repr_t)
//   requires record_perm record repr
//   returns r0:erased engine_record_repr
//   ensures engine_record_perm (Engine_record?.r record) r0 ** pure(repr == Engine_repr r0)
// {
//   let r = Engine_record?.r record;
//   match (reveal repr) { 
//   Engine_repr r0 -> {admit()}
//   _ -> {admit()}
//   }
// }
// ```
assume val get_l0_record_perm (record:record_t{L0_record? record}) (repr:erased repr_t)
  : stt_ghost (erased l0_record_repr) emp_inames
              (record_perm record repr)
              (fun r0 -> l0_record_perm (L0_record?.r record) r0 
                      ** pure(reveal repr == L0_repr r0))

(* Global State *)

let ctxt_hndl_t = U32.t
let sid_t = U32.t

// The type of a hash table tupled with a lock storing permission on the table. 
type locked_ht_t (s:pht_sig_us) = ht:ht_t s & L.lock (exists_ (fun pht -> models s ht pht))
// The type of a session ID (SID) tupled with a lock storing permission on the SID
type locked_sid_t = r:R.ref sid_t & L.lock (exists_ (fun n -> R.pts_to r full_perm n))

let dpe_hashf : ctxt_hndl_t -> US.t = admit()
let sht_len : pos_us = admit()
let cht_len : pos_us = admit()
// Signature for a context table, which maps a context handle to a locked context
let cht_sig : pht_sig_us = mk_pht_sig_us ctxt_hndl_t locked_context_t dpe_hashf
// Signature for a session table, which map a session ID to a context table
let sht_sig : pht_sig_us = mk_pht_sig_us sid_t (locked_ht_t cht_sig) dpe_hashf 


// Function for allocating a locked hash table
```pulse
fn alloc_ht (#s:pht_sig_us) (l:pos_us)
  requires emp
  returns _:locked_ht_t s
  ensures emp
{
  let ht = HT.alloc #s l;
  let lk = L.new_lock (exists_ (fun pht -> models s ht pht));
  ((| ht, lk |) <: locked_ht_t s)
}
```
// Function for allocating a locked session ID
```pulse
fn alloc_sid (_:unit)
  requires emp
  returns _:locked_sid_t
  ensures emp
{
  let locked_sid = R.alloc #sid_t 0ul;
  let lk = L.new_lock (exists_ (fun n -> R.pts_to locked_sid full_perm n));
  ((| locked_sid, lk |) <: locked_sid_t)
}
```

// The global session table, which associates a session ID with a context table for that session
let locked_sht : locked_ht_t sht_sig = run_stt(alloc_ht #sht_sig sht_len)
// The global session ID counter, which tracks what the next session ID is
let locked_sid : locked_sid_t = run_stt(alloc_sid ())


(* ----------- IMPLEMENTATION ----------- *)

(*
  OpenSession: Part of DPE API 
  Create a context table and context table lock for the new session. 
  Add the context table lock to the session table. Return the session
  ID or None upon failure
  NOTE: Current implementation disregards session protocol 
*)
```pulse
fn open_session' (_:unit)
  requires emp
  returns _:option sid_t
  ensures emp
{
  let cht = alloc_ht #cht_sig cht_len;

  let sht_lk = dsnd locked_sht;
  let sid_lk = dsnd locked_sid;

  L.acquire #(exists_ (fun n -> R.pts_to (dfst locked_sid) full_perm n)) sid_lk;
  L.acquire #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;

  let sid = !(dfst locked_sid);

  with pht. assert (models sht_sig (dfst locked_sht) pht);

  let b = not_full #sht_sig #pht (dfst locked_sht);

  if b {
    let r = HT.insert #sht_sig #pht (dfst locked_sht) sid cht;
    with pht'. unfold (maybe_update r sht_sig (dfst locked_sht) pht pht');
    if r {
      assert (HT.models sht_sig (dfst locked_sht) (PHT.insert pht sid cht));
      // dfst locked_sid := sid + 1ul; // FIXME: check whether sum fits into a U32
      L.release #(exists_ (fun n -> R.pts_to (dfst locked_sid) full_perm n)) sid_lk;
      L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
      Some sid
    } else {
      // ERROR - insert failed
      assert (HT.models sht_sig (dfst locked_sht) pht);
      L.release #(exists_ (fun n -> R.pts_to (dfst locked_sid) full_perm n)) sid_lk;
      L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
      None #sid_t
    }
  } else {
    // ERROR - table full
    L.release #(exists_ (fun n -> R.pts_to (dfst locked_sid) full_perm n)) sid_lk;
    L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
    None #sid_t
  }
}
```
let open_session = open_session'

assume
val drop (p:vprop)
    : stt unit p (fun _ -> emp)
```pulse
fn disable_uds (_:unit) 
    requires uds_is_enabled
    ensures emp
{
    drop uds_is_enabled
}
```

```pulse 
fn destroy_ctxt (ctxt:context_t)
  requires context_perm ctxt
  ensures emp
{
  match ctxt {
  Engine_context c -> {
    rewrite (context_perm ctxt) as (engine_context_perm c);
    unfold (engine_context_perm c);
    A.zeroize uds_len c.uds;
    A.free c.uds;
  }
  L0_context c -> {
    rewrite (context_perm ctxt) as (l0_context_perm c);
    unfold (l0_context_perm c);
    with s. assert (A.pts_to c.cdi full_perm s);
    A.zeroize dice_digest_len c.cdi;
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
  }}
}
```

```pulse 
fn destroy_locked_ctxt (locked_ctxt:locked_context_t)
  requires emp
  ensures emp
{
  let ctxt = dfst locked_ctxt;
  let ctxt_lk = dsnd locked_ctxt;
  L.acquire #(context_perm ctxt) ctxt_lk;
  destroy_ctxt ctxt;
}
```

(*
  DestroyContext: Part of DPE API 
  Destroy the context pointed to by the handle by freeing the
  arrays in the context (zeroize the UDS, if applicable). Return
  boolean indicating success. 
  NOTE: Current implementation disregards session protocol 
*)
```pulse
fn destroy_context' (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
  requires emp
  returns b:bool
  ensures emp
{
  let sht_lk = dsnd locked_sht;
  L.acquire #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;

  with spht. assert (models sht_sig (dfst locked_sht) spht);

  let res = HT.lookup #sht_sig #spht (dfst locked_sht) sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> {
      let cht_lk = dsnd locked_cht;
      L.acquire #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
      with cpht0. assert (models cht_sig (dfst locked_cht) cpht0);

      let res = HT.lookup #cht_sig #cpht0 (dfst locked_cht) ctxt_hndl;
      if (fst res) {
        let opt_locked_ctxt = snd res;
        match opt_locked_ctxt {
        Some locked_ctxt -> {
          destroy_locked_ctxt locked_ctxt;
          L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
          L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
          true
        }
        None -> {
          // ERROR - bad context handle
          L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
          L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
          false
        }}
      } else {
        // ERROR - lookup failed
        L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
        L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
        false
      }}
    None -> {
      // ERROR - bad session ID
      L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
      false
    }}
  } else {
    // ERROR - lookup failed
    L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
    false
  }
}
```
let destroy_context = destroy_context'

```pulse
fn ctxt_hndl_do_nothing (k:ctxt_hndl_t)
  requires emp
  ensures emp
{
  ()
}
```

(* 
  CloseSession: Part of DPE API 
  Destroy the context table for the session and remove the reference
  to it from the session table. Return boolean indicating success. 
  NOTE: Current implementation disregards session protocol 
*)
```pulse
fn close_session' (sid:sid_t)
  requires emp
  returns b:bool
  ensures emp
{
  let sht_lk = dsnd locked_sht;
  L.acquire #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;

  with pht. assert (models sht_sig (dfst locked_sht) pht);

  let res = HT.lookup #sht_sig #pht (dfst locked_sht) sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> { 
      let cht_lk = dsnd locked_cht;
      // Note: We don't release this lock because we give up permission
      // on the cht when we deallocate it
      L.acquire #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
      dealloc #cht_sig (dfst locked_cht) cht_len destroy_locked_ctxt ctxt_hndl_do_nothing;
      let b = HT.delete #sht_sig #pht (dfst locked_sht) sid;
      with pht'. unfold (maybe_update b sht_sig (dfst locked_sht) pht pht');
      if b {
        assert (models sht_sig (dfst locked_sht) (PHT.delete pht sid));
        L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
        b
      } else {
        assert (models sht_sig (dfst locked_sht) pht);
        L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
        b
      }
    }
    None -> {
      // ERROR - bad session ID
      L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
      false
    }}
  } else {
    // ERROR - lookup failed
    L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
    false
  }
}
```
let close_session = close_session'

// TODO: 
let prng (_:unit) : U32.t = admit()

```pulse
fn init_engine_ctxt (uds:A.larray U8.t (US.v uds_len)) (#p:perm)
  requires A.pts_to uds p uds_bytes
        ** uds_is_enabled
  returns _:locked_context_t
  ensures A.pts_to uds p uds_bytes
{
  let uds_buf = A.alloc 0uy uds_len;
  memcpy uds_len uds uds_buf;
  disable_uds ();
  let engine_context = mk_engine_context uds_buf;

  rewrite (A.pts_to uds_buf full_perm uds_bytes) 
    as (A.pts_to engine_context.uds full_perm uds_bytes);
  fold (engine_context_perm engine_context);

  let ctxt = mk_engine_context_t engine_context;

  rewrite (engine_context_perm engine_context) as (context_perm ctxt);

  let ctxt_lk = L.new_lock (context_perm ctxt);
  ((| ctxt, ctxt_lk |) <: locked_context_t)
}
```

```pulse
fn _init_l0_ctxt (cdi:A.larray U8.t (US.v dice_digest_len)) (#s:erased (elseq U8.t dice_digest_len))
  requires A.pts_to cdi full_perm s
        ** pure (A.is_full_array cdi)
  returns _:locked_context_t
  ensures emp
{
  let cdi_buf = A.alloc 0uy dice_digest_len;
  memcpy dice_digest_len cdi cdi_buf;
  A.zeroize dice_digest_len cdi;
  A.free cdi;

  let l0_context = mk_l0_context cdi_buf;
  rewrite (A.pts_to cdi_buf full_perm s)
    as (A.pts_to l0_context.cdi full_perm s);
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
  in the current session's context table. Return the context handle upon
  success and None upon failure. 
*)
```pulse
fn initialize_context' (sid:sid_t) (uds:A.larray U8.t (US.v uds_len)) (#p:perm)
  requires A.pts_to uds p uds_bytes
        ** uds_is_enabled
  returns _:option ctxt_hndl_t
  ensures A.pts_to uds p uds_bytes
{
  let locked_context = init_engine_ctxt uds;
  let ctxt_hndl = prng ();

  let sht_lk = dsnd locked_sht;
  L.acquire #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;

  with spht. assert (models sht_sig (dfst locked_sht) spht);

  let res = HT.lookup #sht_sig #spht (dfst locked_sht) sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> {
      let cht_lk = dsnd locked_cht;
      L.acquire #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;

      with cpht. assert (models cht_sig (dfst locked_cht) cpht);
      let b = not_full #cht_sig #cpht (dfst locked_cht);
      if b {
        let r = HT.insert #cht_sig #cpht (dfst locked_cht) ctxt_hndl locked_context;
        with cpht'. unfold (maybe_update r cht_sig (dfst locked_cht) cpht cpht');
        if r {
          assert (models cht_sig (dfst locked_cht) (PHT.insert cpht ctxt_hndl locked_context));
          L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
          L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
          Some ctxt_hndl
        } else {
          // ERROR - insert failed
          assert (models cht_sig (dfst locked_cht) cpht);
          L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
          L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;  
          None #ctxt_hndl_t     
        }
      } else {
        // ERROR - table full
        L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
        L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
        None #ctxt_hndl_t
      }}
    None -> {
      // ERROR - bad session ID
      L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
      None #ctxt_hndl_t
    }}
  } else {
    // ERROR - lookup failed
    L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
    None #ctxt_hndl_t
  }
}
```
let initialize_context = initialize_context'

(*
  RotateContextHandle: Part of DPE API 
  Invalidate the current context handle and replace it with a new context
  handle. Return the context handle upon success and None upon failure.
*)
```pulse
fn rotate_context_handle' (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
  requires emp
  returns _:option ctxt_hndl_t
  ensures emp
{
  let new_ctxt_hndl = prng ();

  let sht_lk = dsnd locked_sht;
  L.acquire #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
  with spht. assert (models sht_sig (dfst locked_sht) spht);

  let res = HT.lookup #sht_sig #spht (dfst locked_sht) sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> {
      let cht_lk = dsnd locked_cht;
      L.acquire #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
      with cpht. assert (models cht_sig (dfst locked_cht) cpht);
      let r = HT.lookup #cht_sig #cpht (dfst locked_cht) ctxt_hndl;
      if (fst r) {
        let opt_locked_ctxt = snd r;
        match opt_locked_ctxt {
        Some locked_context -> {
          let b = not_full #cht_sig #cpht (dfst locked_cht);
          if b {
            let r = HT.insert #cht_sig #cpht (dfst locked_cht) new_ctxt_hndl locked_context;
            with cpht'. unfold (maybe_update r cht_sig (dfst locked_cht) cpht cpht'); // FIXME: why doesn't this work if we explicitly specify cpht and cpht'
            if r {
              assert (models cht_sig (dfst locked_cht) (PHT.insert cpht new_ctxt_hndl locked_context));
              let d = HT.delete #cht_sig #(PHT.insert cpht new_ctxt_hndl locked_context) (dfst locked_cht) ctxt_hndl;
              with x y. unfold (maybe_update d cht_sig (dfst locked_cht) x y); 
              if d {
                assert (models cht_sig (dfst locked_cht) (PHT.delete (PHT.insert cpht new_ctxt_hndl locked_context) ctxt_hndl));
                L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
                L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
                Some new_ctxt_hndl
              } else {
                // ERROR - delete failed
                assert (models cht_sig (dfst locked_cht) (PHT.insert cpht new_ctxt_hndl locked_context));
                L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
                L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
                None #ctxt_hndl_t
              }
            } else {
              // ERROR - insert failed
              assert (models cht_sig (dfst locked_cht) cpht);
              L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
              L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;  
              None #ctxt_hndl_t
          }} else {
              // ERROR - table full
              L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
              L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
              None #ctxt_hndl_t
          }}
        None -> {
          // ERROR - bad context handle
          L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
          L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
          None #ctxt_hndl_t 
        }}
      } else {
        // ERROR - lookup failed
        L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
        L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
        None #ctxt_hndl_t 
      }}
    None -> {
      // ERROR - lookup context table failed
      L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
      None #ctxt_hndl_t 
    }}
  } else {
    // ERROR - lookup context table failed
    L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
    None #ctxt_hndl_t 
  }
}
```
let rotate_context_handle = rotate_context_handle'

(*
  DeriveChild: Part of DPE API 
  Execute the DICE layer associated with the current context and produce a 
  new context. Destroy the current context in the current session's context table 
  and store the new context in the table. Return the new context handle upon
  success and None upon failure. 
*)
```pulse
fn derive_child' (sid:sid_t) (ctxt_hndl:ctxt_hndl_t) (record:record_t) (#repr:erased repr_t)
  requires record_perm record repr
  returns _:option ctxt_hndl_t
  ensures record_perm record repr
{
  let new_ctxt_hndl = prng ();

  let sht_lk = dsnd locked_sht;
  L.acquire #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
  with spht. assert (models sht_sig (dfst locked_sht) spht);

  let res = HT.lookup #sht_sig #spht (dfst locked_sht) sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> {
      let cht_lk = dsnd locked_cht;
      L.acquire #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
      with cpht. assert (models cht_sig (dfst locked_cht) cpht);

      let r = HT.lookup #cht_sig #cpht (dfst locked_cht) ctxt_hndl;
      if (fst r) {
        let opt_locked_ctxt = snd r;
        match opt_locked_ctxt {
        Some locked_ctxt -> {
        let ctxt = dfst locked_ctxt;
        let ctxt_lk = dsnd locked_ctxt;
        L.acquire #(context_perm ctxt) ctxt_lk;

        match ctxt {
        Engine_context c -> {
          // NOTE: we won't eventually release engine_context_perm because we won't 
          // own it anymore -- we will disable the uds and free the uds array
          rewrite (context_perm ctxt) as (engine_context_perm c);
          unfold (engine_context_perm c);

          match record {
          Engine_record r -> {
            let r0 = get_engine_record_perm record repr; 
            rewrite (engine_record_perm (Engine_record?.r record) r0)
              as (engine_record_perm r r0);
            
            let cdi = A.alloc 0uy dice_digest_len;
            let ret = EngineCore.engine_main cdi c.uds r;
            with s. assert (A.pts_to cdi full_perm s);
            fold (engine_context_perm c);
            rewrite (engine_context_perm c) as (context_perm ctxt);
            destroy_ctxt ctxt;

            match ret {
            DICE_SUCCESS -> {
              let new_locked_context = init_l0_ctxt cdi;
              
              let d = HT.delete #cht_sig #cpht (dfst locked_cht) ctxt_hndl;
              with cpht'. unfold (maybe_update d cht_sig (dfst locked_cht) cpht cpht');
              if d {
                assert (models cht_sig (dfst locked_cht) (PHT.delete cpht ctxt_hndl));
                let b = not_full #cht_sig #(PHT.delete cpht ctxt_hndl) (dfst locked_cht);
                if b {
                  let i = HT.insert #cht_sig #(PHT.delete cpht ctxt_hndl) (dfst locked_cht) new_ctxt_hndl new_locked_context; 
                  with x y. unfold (maybe_update i cht_sig (dfst locked_cht) x y);
                  if i {
                    assert (models cht_sig (dfst locked_cht) (PHT.insert (PHT.delete cpht ctxt_hndl) new_ctxt_hndl new_locked_context));
                    rewrite (engine_record_perm r r0) as (record_perm record repr);
                    L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
                    L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
                    Some new_ctxt_hndl
                  } else {
                    // ERROR - insert failed
                    assert (models cht_sig (dfst locked_cht) (PHT.delete cpht ctxt_hndl));
                    rewrite (engine_record_perm r r0) as (record_perm record repr);
                    L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
                    L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
                    None #ctxt_hndl_t
                }} else {
                  // ERROR - table full
                  rewrite (engine_record_perm r r0) as (record_perm record repr);
                  L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
                  L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
                  None #ctxt_hndl_t
              }} else {
                // ERROR - delete failed
                assert (models cht_sig (dfst locked_cht) cpht);
                rewrite (engine_record_perm r r0) as (record_perm record repr);
                L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
                L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
                None #ctxt_hndl_t
              }}
            DICE_ERROR -> {
              // ERROR - DICE engine failed
              A.zeroize dice_digest_len cdi;
              A.free cdi;
              rewrite (engine_record_perm r r0) as (record_perm record repr);
              L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
              L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
              None #ctxt_hndl_t
            }}}
          _ -> {
            // ERROR - record should have type (Engine_record r)
            fold (engine_context_perm c);
            rewrite (engine_context_perm c) as (context_perm ctxt);
            destroy_ctxt ctxt;
            L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
            L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
            None #ctxt_hndl_t
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
            let r0 = get_l0_record_perm record repr;
            rewrite (l0_record_perm (L0_record?.r record) r0)
              as (l0_record_perm r r0);

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

            let deviceID_pub = A.alloc 0uy v32us;
            let deviceID_priv = A.alloc 0uy v32us;
            let aliasKey_pub = A.alloc 0uy v32us;
            let aliasKey_priv = A.alloc 0uy v32us;
            let deviceIDCSR = A.alloc 0uy deviceIDCSR_len;
            let aliasKeyCRT = A.alloc 0uy aliasKeyCRT_len;
            
            L0Core.l0_main  c.cdi deviceID_pub deviceID_priv 
                            aliasKey_pub aliasKey_priv 
                            aliasKeyTBS_len aliasKeyCRT_len aliasKeyCRT 
                            deviceIDCRI_len deviceIDCSR_len deviceIDCSR r;
            fold (l0_context_perm c);
            rewrite (l0_context_perm c) as (context_perm ctxt);
            destroy_ctxt ctxt;

            with (s1:elseq U8.t v32us). assert (A.pts_to aliasKey_priv full_perm s1);
            let new_locked_context = init_l1_ctxt deviceIDCSR_len aliasKeyCRT_len 
                                                  deviceID_priv deviceID_pub
                                                  aliasKey_priv aliasKey_pub 
                                                  deviceIDCSR aliasKeyCRT;
            A.free deviceID_pub;
            A.free deviceID_priv;
            A.free aliasKey_pub;
            A.free aliasKey_priv;
            A.free deviceIDCSR;
            A.free aliasKeyCRT;
            
            let d = HT.delete #cht_sig #cpht (dfst locked_cht) ctxt_hndl;
            with x y. unfold (maybe_update d cht_sig (dfst locked_cht) x y);
            if d {
              assert (models cht_sig (dfst locked_cht) (PHT.delete cpht ctxt_hndl));
              let b = not_full #cht_sig #(PHT.delete cpht ctxt_hndl) (dfst locked_cht);
              if b {
                let i = HT.insert #cht_sig #(PHT.delete cpht ctxt_hndl) (dfst locked_cht) new_ctxt_hndl new_locked_context;
                with x y. unfold (maybe_update i cht_sig (dfst locked_cht) x y);
                if i {
                  assert (models cht_sig (dfst locked_cht) (PHT.insert (PHT.delete cpht ctxt_hndl) new_ctxt_hndl new_locked_context));
                  rewrite (l0_record_perm r r0) as (record_perm record repr);
                  L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
                  L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
                  Some new_ctxt_hndl
                } else {
                  // ERROR - insert failed
                  assert (models cht_sig (dfst locked_cht) (PHT.delete cpht ctxt_hndl));
                  rewrite (l0_record_perm r r0) as (record_perm record repr);
                  L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
                  L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
                  None #ctxt_hndl_t
              }} else {
                // ERROR - table full
                rewrite (l0_record_perm r r0) as (record_perm record repr);
                L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
                L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
                None #ctxt_hndl_t
            }} else {
              // ERROR - delete failed
              assert (models cht_sig (dfst locked_cht) cpht);
              rewrite (l0_record_perm r r0) as (record_perm record repr);
              L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
              L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
              None #ctxt_hndl_t
            }}
          _ -> {
            // ERROR - record should have type (L0_record r)
            fold (l0_context_perm c);
            rewrite (l0_context_perm c) as (context_perm ctxt);
            destroy_ctxt ctxt;
            L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
            L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
            None #ctxt_hndl_t
          }}
        }
        _ -> { 
          // ERROR - cannot invoke DeriveChild with L1 context
          L.release #(context_perm ctxt) ctxt_lk;
          L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
          L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
          None #ctxt_hndl_t
        }}}
        None -> { 
        // ERROR - bad context handle
        L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
        L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
        None #ctxt_hndl_t
        }}
      } else {
        // ERROR - lookup failed
        L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
        L.release #(exists_ (fun pht -> models cht_sig (dfst locked_cht) pht)) cht_lk;
        None #ctxt_hndl_t
      }}
    None -> { 
    // ERROR - bad session ID
    L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
    None #ctxt_hndl_t
    }}
  } else {
    // ERROR - lookup failed
    L.release #(exists_ (fun pht -> models sht_sig (dfst locked_sht) pht)) sht_lk;
    None #ctxt_hndl_t
  }
}
```
let derive_child = derive_child'