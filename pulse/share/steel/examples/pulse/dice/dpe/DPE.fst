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
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HT = Pulse.Lib.HashTable
module PHT = FStar.HashTable
open Pulse.Class.BoundedIntegers

assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a

(* Engine Context *)
noeq
type engine_context_t = { 
  uds: A.larray U8.t (US.v uds_len); 
}

let engine_context_perm (c:engine_context_t) : vprop
  = A.pts_to c.uds full_perm uds_bytes ** 
    pure (A.is_full_array c.uds)

let mk_engine_context_t uds : engine_context_t = {uds}

(* L0 Context *)
noeq
type l0_context_t = { 
  cdi:A.larray U8.t (US.v dice_digest_len); 
}

let mk_l0_context_t cdi : l0_context_t = {cdi}

type l0_context_repr_t = {
  cdi:elseq U8.t dice_digest_len;
  repr:engine_record_repr;
}

let mk_l0_context_repr_t
  (cdi:erased (elseq U8.t dice_digest_len)) 
  (repr:erased engine_record_repr) 
: erased l0_context_repr_t 
= {cdi; repr}

let l0_context_perm (c:l0_context_t) (r:l0_context_repr_t): vprop
  = A.pts_to c.cdi full_perm r.cdi **
    pure (A.is_full_array c.cdi
       /\ cdi_functional_correctness r.cdi r.repr
       /\ l0_is_authentic r.repr)


(* L1 Context *)
noeq
type l1_context_t = { deviceID_priv: A.larray U8.t (US.v v32us);
                    deviceID_pub: A.larray U8.t (US.v v32us);   
                    aliasKey_priv: A.larray U8.t (US.v v32us);
                    aliasKey_pub: A.larray U8.t (US.v v32us);
                    aliasKeyCRT: A.array U8.t;
                    deviceIDCSR: A.array U8.t; }

let mk_l1_context_t deviceID_priv deviceID_pub aliasKey_priv aliasKey_pub aliasKeyCRT deviceIDCSR 
: l1_context_t
= { deviceID_priv; deviceID_pub; aliasKey_priv; aliasKey_pub; aliasKeyCRT; deviceIDCSR }

noeq
type l1_context_repr_t = {
  deviceID_label_len: hkdf_lbl_len;
  aliasKey_label_len: hkdf_lbl_len;
  deviceID_priv: elseq U8.t v32us;
  deviceID_pub: elseq U8.t v32us;
  aliasKey_priv: elseq U8.t v32us;
  aliasKey_pub:elseq U8.t v32us;
  aliasKeyCRT_len:SZ.t;
  aliasKeyCRT: elseq U8.t aliasKeyCRT_len;
  deviceIDCSR_len:SZ.t;
  deviceIDCSR:elseq U8.t deviceIDCSR_len;
  cdi:elseq U8.t dice_digest_len;
  repr:l0_record_repr;
  deviceIDCSR_ingredients: deviceIDCSR_ingredients_t;
  aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t;
}

let mk_l1_context_repr_t 
  (deviceID_label_len:erased hkdf_lbl_len)
  (aliasKey_label_len:erased hkdf_lbl_len)
  (deviceID_priv:erased (elseq U8.t v32us))
  (deviceID_pub:erased (elseq U8.t v32us))
  (aliasKey_priv:erased (elseq U8.t v32us))
  (aliasKey_pub:erased (elseq U8.t v32us))
  (aliasKeyCRT_len:erased SZ.t)
  (aliasKeyCRT:erased (elseq U8.t aliasKeyCRT_len))
  (deviceIDCSR_len:erased SZ.t)
  (deviceIDCSR:erased (elseq U8.t deviceIDCSR_len))
  (cdi:erased (elseq U8.t dice_digest_len))
  (repr:erased l0_record_repr)
  (deviceIDCSR_ingredients:erased deviceIDCSR_ingredients_t)
  (aliasKeyCRT_ingredients:erased aliasKeyCRT_ingredients_t)
: erased l1_context_repr_t 
= {deviceID_label_len; aliasKey_label_len; deviceID_priv; deviceID_pub; aliasKey_priv;
  aliasKey_pub; aliasKeyCRT_len; aliasKeyCRT; deviceIDCSR_len; deviceIDCSR;
  cdi; repr; deviceIDCSR_ingredients; aliasKeyCRT_ingredients}

let l1_context_perm (c:l1_context_t) (r:l1_context_repr_t)
  : vprop
  = A.pts_to c.deviceID_priv full_perm r.deviceID_priv **
    A.pts_to c.deviceID_pub full_perm r.deviceID_pub **
    A.pts_to c.aliasKey_priv full_perm r.aliasKey_priv **
    A.pts_to c.aliasKey_pub full_perm r.aliasKey_pub **
    A.pts_to c.aliasKeyCRT full_perm r.aliasKeyCRT **
    A.pts_to c.deviceIDCSR full_perm r.deviceIDCSR **
    pure (
      valid_hkdf_ikm_len dice_digest_len /\
      aliasKey_functional_correctness
        dice_hash_alg dice_digest_len r.cdi r.repr.fwid
        r.aliasKey_label_len r.repr.aliasKey_label 
        r.aliasKey_pub r.aliasKey_priv /\
      deviceIDCSR_functional_correctness 
        dice_hash_alg dice_digest_len r.cdi
        r.deviceID_label_len r.repr.deviceID_label r.deviceIDCSR_ingredients 
        r.deviceIDCSR_len r.deviceIDCSR /\       
      aliasKeyCRT_functional_correctness 
        dice_hash_alg dice_digest_len r.cdi r.repr.fwid
        r.deviceID_label_len r.repr.deviceID_label r.aliasKeyCRT_ingredients 
        r.aliasKeyCRT_len r.aliasKeyCRT r.aliasKey_pub /\
      A.is_full_array c.deviceID_priv /\
      A.is_full_array c.deviceID_pub /\
      A.is_full_array c.aliasKey_priv /\
      A.is_full_array c.aliasKey_pub /\
      A.is_full_array c.aliasKeyCRT /\
      A.is_full_array c.deviceIDCSR
    )  

(* Generic Context *)    // this is called an enumeration
noeq
type context_t = 
  | Engine_context : c:engine_context_t -> context_t
  | L0_context     : c:l0_context_t -> context_t
  | L1_context     : c:l1_context_t -> context_t

let mk_context_t_engine c = Engine_context c
let mk_context_t_l0 c = L0_context c
let mk_context_t_l1 c = L1_context c

noeq
type context_repr_t = 
  | Engine_context_repr : context_repr_t
  | L0_context_repr     : r:l0_context_repr_t -> context_repr_t
  | L1_context_repr     : r:l1_context_repr_t -> context_repr_t

let mk_context_repr_t_l0 (r:erased l0_context_repr_t) 
: erased context_repr_t = L0_context_repr r
let mk_context_repr_t_l1 (r:erased l1_context_repr_t) 
: erased context_repr_t = L1_context_repr r

let context_perm (context:context_t) (repr:context_repr_t): vprop = 
  match context with
  | Engine_context c -> engine_context_perm c
  | L0_context c -> (
    match repr with 
    | L0_context_repr r -> l0_context_perm c r
    | _ -> pure(false)
  )
  | L1_context c -> (
    match repr with
    | L1_context_repr r -> l1_context_perm c r
    | _ -> pure(false)
  )

assume val get_l0_context_perm (context:context_t{L0_context? context}) (repr:erased context_repr_t)
  : stt_ghost (erased l0_context_repr_t) emp_inames
              (context_perm context repr)
              (fun r -> l0_context_perm (L0_context?.c context) r
                      ** pure(reveal repr == L0_context_repr r))

assume val get_l1_context_perm (context:context_t{L1_context? context}) (repr:erased context_repr_t)
  : stt_ghost (erased l1_context_repr_t) emp_inames
              (context_perm context repr)
              (fun r -> l1_context_perm (L1_context?.c context) r
                      ** pure(reveal repr == L1_context_repr r))

// In the implmentation, we store contexts as values in a global hash table
// so we need a way to store and retrieve permission on the context. We do this
// by keeping a tuple of the context along with a lock on the context permission
let locked_context_t = c:context_t 
                     & r:erased context_repr_t 
                     & L.lock (context_perm c r)

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

  let sht_lk = locked_sht._2;
  let sid_lk = locked_sid._2;

  L.acquire #(exists_ (fun n -> R.pts_to locked_sid._1 full_perm n)) sid_lk;
  L.acquire #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;

  let sid = !locked_sid._1;

  with pht. assert (models sht_sig locked_sht._1 pht);

  let b = not_full #sht_sig #pht locked_sht._1;

  if b {
    let r = HT.insert #sht_sig #pht locked_sht._1 sid cht;
    with pht'. unfold (maybe_update r sht_sig locked_sht._1 pht pht');
    if r {
      assert (HT.models sht_sig locked_sht._1 (PHT.insert pht sid cht));
      let opt_inc = sid `safe_add` 1ul;
      match opt_inc {
      Some inc -> {
        locked_sid._1 := inc;
        L.release #(exists_ (fun n -> R.pts_to locked_sid._1 full_perm n)) sid_lk;
        L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
        Some sid
      }
      None -> {
        // ERROR - increment session ID failed
        L.release #(exists_ (fun n -> R.pts_to locked_sid._1 full_perm n)) sid_lk;
        L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
        None #sid_t
      }}
    } else {
      // ERROR - insert failed
      assert (HT.models sht_sig locked_sht._1 pht);
      L.release #(exists_ (fun n -> R.pts_to locked_sid._1 full_perm n)) sid_lk;
      L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
      None #sid_t
    }
  } else {
    // ERROR - table full
    L.release #(exists_ (fun n -> R.pts_to locked_sid._1 full_perm n)) sid_lk;
    L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
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
fn destroy_ctxt (ctxt:context_t) (#repr:erased context_repr_t)
  requires context_perm ctxt repr
  ensures emp
{
  match ctxt {
  Engine_context c -> {
    rewrite (context_perm ctxt repr) as (engine_context_perm c);
    unfold (engine_context_perm c);
    A.zeroize uds_len c.uds;
    A.free c.uds;
  }
  L0_context c -> {
    let r = get_l0_context_perm ctxt repr;
    rewrite (l0_context_perm (L0_context?.c ctxt) r)
      as (l0_context_perm c r);
    unfold (l0_context_perm c r);
    with s. assert (A.pts_to c.cdi full_perm s);
    A.zeroize dice_digest_len c.cdi;
    A.free c.cdi;
  }
  L1_context c -> {
    let r = get_l1_context_perm ctxt repr;
    rewrite (l1_context_perm (L1_context?.c ctxt) r)
      as (l1_context_perm c r);
    unfold (l1_context_perm c r);
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
  let ctxt = locked_ctxt._1;
  let repr = locked_ctxt._2;
  let ctxt_lk = locked_ctxt._3;
  L.acquire #(context_perm ctxt repr) ctxt_lk;
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
  let sht_lk = locked_sht._2;
  L.acquire #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;

  with spht. assert (models sht_sig locked_sht._1 spht);

  let res = HT.lookup #sht_sig #spht locked_sht._1 sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> {
      let cht_lk = locked_cht._2;
      L.acquire #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
      with cpht0. assert (models cht_sig locked_cht._1 cpht0);

      let res = HT.lookup #cht_sig #cpht0 locked_cht._1 ctxt_hndl;
      if (fst res) {
        let opt_locked_ctxt = snd res;
        match opt_locked_ctxt {
        Some locked_ctxt -> {
          destroy_locked_ctxt locked_ctxt;
          L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
          L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
          true
        }
        None -> {
          // ERROR - bad context handle
          L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
          L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
          false
        }}
      } else {
        // ERROR - lookup failed
        L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
        L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
        false
      }}
    None -> {
      // ERROR - bad session ID
      L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
      false
    }}
  } else {
    // ERROR - lookup failed
    L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
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
  let sht_lk = locked_sht._2;
  L.acquire #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;

  with pht. assert (models sht_sig locked_sht._1 pht);

  let res = HT.lookup #sht_sig #pht locked_sht._1 sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> { 
      let cht_lk = locked_cht._2;
      // Note: We don't release this lock because we give up permission
      // on the cht when we deallocate it
      L.acquire #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
      dealloc #cht_sig locked_cht._1 cht_len destroy_locked_ctxt ctxt_hndl_do_nothing;
      let b = HT.delete #sht_sig #pht locked_sht._1 sid;
      with pht'. unfold (maybe_update b sht_sig locked_sht._1 pht pht');
      if b {
        assert (models sht_sig locked_sht._1 (PHT.delete pht sid));
        L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
        b
      } else {
        assert (models sht_sig locked_sht._1 pht);
        L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
        b
      }
    }
    None -> {
      // ERROR - bad session ID
      L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
      false
    }}
  } else {
    // ERROR - lookup failed
    L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
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
  let engine_context = mk_engine_context_t uds_buf;

  rewrite (A.pts_to uds_buf full_perm uds_bytes) 
    as (A.pts_to engine_context.uds full_perm uds_bytes);
  fold (engine_context_perm engine_context);

  let ctxt = mk_context_t_engine engine_context;
  rewrite (engine_context_perm engine_context) 
    as (context_perm ctxt Engine_context_repr);

  let ctxt_lk = L.new_lock (context_perm ctxt Engine_context_repr);
  ((| ctxt, hide Engine_context_repr, ctxt_lk |) <: locked_context_t)
}
```

```pulse
fn init_l0_ctxt (cdi:A.larray U8.t (US.v dice_digest_len)) 
  (#engine_repr:erased engine_record_repr)
  (#s:erased (elseq U8.t dice_digest_len))
  (_:squash(cdi_functional_correctness s engine_repr
         /\ l0_is_authentic engine_repr))
  requires A.pts_to cdi full_perm s
        ** pure (A.is_full_array cdi)
  returns _:locked_context_t
  ensures emp
{
  let cdi_buf = A.alloc 0uy dice_digest_len;
  memcpy dice_digest_len cdi cdi_buf;
  A.zeroize dice_digest_len cdi;
  A.free cdi;

  let l0_context = mk_l0_context_t cdi_buf;
  let l0_context_repr = mk_l0_context_repr_t s engine_repr;
  rewrite (A.pts_to cdi_buf full_perm s)
    as (A.pts_to l0_context.cdi full_perm s);
  fold (l0_context_perm l0_context l0_context_repr);

  let ctxt = mk_context_t_l0 l0_context;
  let repr = mk_context_repr_t_l0 l0_context_repr;
  rewrite (l0_context_perm l0_context l0_context_repr) 
    as (context_perm ctxt repr);

  let ctxt_lk = L.new_lock (context_perm ctxt repr);
  ((| ctxt, repr, ctxt_lk |) <: locked_context_t)
}
```

```pulse
fn init_l1_ctxt (deviceIDCSR_len: US.t) (aliasKeyCRT_len: US.t) 
                (deviceID_priv: A.larray U8.t (US.v v32us)) (deviceID_pub: A.larray U8.t (US.v v32us))
                (aliasKey_priv: A.larray U8.t (US.v v32us)) (aliasKey_pub: A.larray U8.t (US.v v32us)) 
                (deviceIDCSR: A.larray U8.t (US.v deviceIDCSR_len)) (aliasKeyCRT: A.larray U8.t (US.v aliasKeyCRT_len))
                (#deviceID_priv0 #deviceID_pub0 #aliasKey_priv0 #aliasKey_pub0: erased (elseq U8.t v32us)) 
                (#deviceIDCSR0:erased (elseq U8.t deviceIDCSR_len))
                (#aliasKeyCRT0:erased (elseq U8.t aliasKeyCRT_len))
                (#deviceID_label_len #aliasKey_label_len: erased hkdf_lbl_len)
                (#cdi:erased (elseq U8.t dice_digest_len))
                (#repr:erased l0_record_repr)
                (#deviceIDCSR_ingredients:erased deviceIDCSR_ingredients_t)
                (#aliasKeyCRT_ingredients:erased aliasKeyCRT_ingredients_t)
                (_:squash(valid_hkdf_ikm_len dice_digest_len
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
                            aliasKeyCRT_len aliasKeyCRT0 aliasKey_pub0))
  requires A.pts_to deviceID_priv full_perm deviceID_priv0 ** 
           A.pts_to deviceID_pub full_perm deviceID_pub0 ** 
           A.pts_to aliasKey_priv full_perm aliasKey_priv0 ** 
           A.pts_to aliasKey_pub full_perm aliasKey_pub0 ** 
           A.pts_to deviceIDCSR full_perm deviceIDCSR0 **
           A.pts_to aliasKeyCRT full_perm aliasKeyCRT0
  returns _:locked_context_t
  ensures 
    A.pts_to deviceID_priv full_perm deviceID_priv0 ** 
    A.pts_to deviceID_pub full_perm deviceID_pub0 **
    A.pts_to aliasKey_priv full_perm aliasKey_priv0 ** 
    A.pts_to aliasKey_pub full_perm aliasKey_pub0 ** 
    A.pts_to deviceIDCSR full_perm deviceIDCSR0 **
    A.pts_to aliasKeyCRT full_perm aliasKeyCRT0
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

  let l1_context = mk_l1_context_t 
    deviceID_priv_buf deviceID_pub_buf aliasKey_priv_buf aliasKey_pub_buf 
    aliasKeyCRT_buf deviceIDCSR_buf;
  let l1_context_repr = mk_l1_context_repr_t 
    deviceID_label_len aliasKey_label_len deviceID_priv0 deviceID_pub0
    aliasKey_priv0 aliasKey_pub0 aliasKeyCRT_len aliasKeyCRT0 deviceIDCSR_len
    deviceIDCSR0 cdi repr deviceIDCSR_ingredients aliasKeyCRT_ingredients;

  rewrite (A.pts_to deviceID_priv_buf full_perm deviceID_priv0 **
           A.pts_to deviceID_pub_buf full_perm deviceID_pub0 **
           A.pts_to aliasKey_priv_buf full_perm aliasKey_priv0 **
           A.pts_to aliasKey_pub_buf full_perm aliasKey_pub0 **
           A.pts_to deviceIDCSR_buf full_perm deviceIDCSR0 **
           A.pts_to aliasKeyCRT_buf full_perm aliasKeyCRT0)
       as (A.pts_to l1_context.deviceID_priv full_perm deviceID_priv0**
           A.pts_to l1_context.deviceID_pub full_perm deviceID_pub0 **
           A.pts_to l1_context.aliasKey_priv full_perm aliasKey_priv0 **
           A.pts_to l1_context.aliasKey_pub full_perm aliasKey_pub0 **
           A.pts_to l1_context.deviceIDCSR full_perm deviceIDCSR0 **
           A.pts_to l1_context.aliasKeyCRT full_perm aliasKeyCRT0);
  fold (l1_context_perm l1_context l1_context_repr);

  let ctxt = mk_context_t_l1 l1_context;
  let repr = mk_context_repr_t_l1 l1_context_repr;
  rewrite (l1_context_perm l1_context l1_context_repr) as (context_perm ctxt repr);
  
  let ctxt_lk = L.new_lock (context_perm ctxt repr);
  ((| ctxt, repr, ctxt_lk |) <: locked_context_t)
}
```

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

  let sht_lk = locked_sht._2;
  L.acquire #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;

  with spht. assert (models sht_sig locked_sht._1 spht);

  let res = HT.lookup #sht_sig #spht locked_sht._1 sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> {
      let cht_lk = locked_cht._2;
      L.acquire #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;

      with cpht. assert (models cht_sig locked_cht._1 cpht);
      let b = not_full #cht_sig #cpht locked_cht._1;
      if b {
        let r = HT.insert #cht_sig #cpht locked_cht._1 ctxt_hndl locked_context;
        with cpht'. unfold (maybe_update r cht_sig locked_cht._1 cpht cpht');
        if r {
          assert (models cht_sig locked_cht._1 (PHT.insert cpht ctxt_hndl locked_context));
          L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
          L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
          Some ctxt_hndl
        } else {
          // ERROR - insert failed
          assert (models cht_sig locked_cht._1 cpht);
          L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
          L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;  
          None #ctxt_hndl_t     
        }
      } else {
        // ERROR - table full
        L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
        L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
        None #ctxt_hndl_t
      }}
    None -> {
      // ERROR - bad session ID
      L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
      None #ctxt_hndl_t
    }}
  } else {
    // ERROR - lookup failed
    L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
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

  let sht_lk = locked_sht._2;
  L.acquire #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
  with spht. assert (models sht_sig locked_sht._1 spht);

  let res = HT.lookup #sht_sig #spht locked_sht._1 sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> {
      let cht_lk = locked_cht._2;
      L.acquire #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
      with cpht. assert (models cht_sig locked_cht._1 cpht);
      let r = HT.lookup #cht_sig #cpht locked_cht._1 ctxt_hndl;
      if (fst r) {
        let opt_locked_ctxt = snd r;
        match opt_locked_ctxt {
        Some locked_context -> {
          let b = not_full #cht_sig #cpht locked_cht._1;
          if b {
            let r = HT.insert #cht_sig #cpht locked_cht._1 new_ctxt_hndl locked_context;
            with cpht'. unfold (maybe_update r cht_sig locked_cht._1 cpht cpht'); // FIXME: why doesn't this work if we explicitly specify cpht and cpht'
            if r {
              assert (models cht_sig locked_cht._1 (PHT.insert cpht new_ctxt_hndl locked_context));
              let d = HT.delete #cht_sig #(PHT.insert cpht new_ctxt_hndl locked_context) locked_cht._1 ctxt_hndl;
              with x y. unfold (maybe_update d cht_sig locked_cht._1 x y); 
              if d {
                assert (models cht_sig locked_cht._1 (PHT.delete (PHT.insert cpht new_ctxt_hndl locked_context) ctxt_hndl));
                L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
                L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
                Some new_ctxt_hndl
              } else {
                // ERROR - delete failed
                assert (models cht_sig locked_cht._1 (PHT.insert cpht new_ctxt_hndl locked_context));
                L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
                L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
                None #ctxt_hndl_t
              }
            } else {
              // ERROR - insert failed
              assert (models cht_sig locked_cht._1 cpht);
              L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
              L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;  
              None #ctxt_hndl_t
          }} else {
              // ERROR - table full
              L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
              L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
              None #ctxt_hndl_t
          }}
        None -> {
          // ERROR - bad context handle
          L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
          L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
          None #ctxt_hndl_t 
        }}
      } else {
        // ERROR - lookup failed
        L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
        L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
        None #ctxt_hndl_t 
      }}
    None -> {
      // ERROR - lookup context table failed
      L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
      None #ctxt_hndl_t 
    }}
  } else {
    // ERROR - lookup context table failed
    L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
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

  let sht_lk = locked_sht._2;
  L.acquire #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
  with spht. assert (models sht_sig locked_sht._1 spht);

  let res = HT.lookup #sht_sig #spht locked_sht._1 sid;
  if (fst res) {
    let opt_locked_cht = snd res;
    match opt_locked_cht {
    Some locked_cht -> {
      let cht_lk = locked_cht._2;
      L.acquire #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
      with cpht. assert (models cht_sig locked_cht._1 cpht);

      let r = HT.lookup #cht_sig #cpht locked_cht._1 ctxt_hndl;
      if (fst r) {
        let opt_locked_ctxt = snd r;
        match opt_locked_ctxt {
        Some locked_ctxt -> {
        let ctxt = locked_ctxt._1;
        let ctxt_repr = locked_ctxt._2;
        let ctxt_lk = locked_ctxt._3;
        L.acquire #(context_perm ctxt ctxt_repr) ctxt_lk;

        match ctxt {
        Engine_context c -> {
          // NOTE: we won't eventually release engine_context_perm because we won't 
          // own it anymore -- we will disable the uds and free the uds array
          rewrite (context_perm ctxt ctxt_repr) as (engine_context_perm c);
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
            rewrite (engine_context_perm c) as (context_perm ctxt ctxt_repr);
            destroy_ctxt ctxt;

            match ret {
            DICE_SUCCESS -> {
              let new_locked_context = init_l0_ctxt cdi #r0 #s ();
              
              let d = HT.delete #cht_sig #cpht locked_cht._1 ctxt_hndl;
              with cpht'. unfold (maybe_update d cht_sig locked_cht._1 cpht cpht');
              if d {
                assert (models cht_sig locked_cht._1 (PHT.delete cpht ctxt_hndl));
                let b = not_full #cht_sig #(PHT.delete cpht ctxt_hndl) locked_cht._1;
                if b {
                  let i = HT.insert #cht_sig #(PHT.delete cpht ctxt_hndl) locked_cht._1 new_ctxt_hndl new_locked_context; 
                  with x y. unfold (maybe_update i cht_sig locked_cht._1 x y);
                  if i {
                    assert (models cht_sig locked_cht._1 (PHT.insert (PHT.delete cpht ctxt_hndl) new_ctxt_hndl new_locked_context));
                    rewrite (engine_record_perm r r0) as (record_perm record repr);
                    L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
                    L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
                    Some new_ctxt_hndl
                  } else {
                    // ERROR - insert failed
                    assert (models cht_sig locked_cht._1 (PHT.delete cpht ctxt_hndl));
                    rewrite (engine_record_perm r r0) as (record_perm record repr);
                    L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
                    L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
                    None #ctxt_hndl_t
                }} else {
                  // ERROR - table full
                  rewrite (engine_record_perm r r0) as (record_perm record repr);
                  L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
                  L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
                  None #ctxt_hndl_t
              }} else {
                // ERROR - delete failed
                assert (models cht_sig locked_cht._1 cpht);
                rewrite (engine_record_perm r r0) as (record_perm record repr);
                L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
                L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
                None #ctxt_hndl_t
              }}
            DICE_ERROR -> {
              // ERROR - DICE engine failed
              A.zeroize dice_digest_len cdi;
              A.free cdi;
              rewrite (engine_record_perm r r0) as (record_perm record repr);
              L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
              L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
              None #ctxt_hndl_t
            }}}
          _ -> {
            // ERROR - record should have type (Engine_record r)
            fold (engine_context_perm c);
            rewrite (engine_context_perm c) as (context_perm ctxt ctxt_repr);
            destroy_ctxt ctxt;
            L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
            L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
            None #ctxt_hndl_t
          }}
        }
        L0_context c -> {
          // NOTE: we won't eventually release l0_context_perm because we won't 
          // own it anymore -- we will free the cdi array
          let cr = get_l0_context_perm ctxt ctxt_repr;
          rewrite (l0_context_perm (L0_context?.c ctxt) cr)
            as (l0_context_perm c cr);
          unfold (l0_context_perm c cr);
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
            fold (l0_context_perm c cr);
            rewrite (l0_context_perm c cr) as (context_perm ctxt ctxt_repr);
            destroy_ctxt ctxt;

            with deviceID_pub1. assert (A.pts_to deviceID_pub full_perm deviceID_pub1);
            with deviceID_priv1. assert (A.pts_to deviceID_priv full_perm deviceID_priv1);
            with aliasKey_pub1. assert (A.pts_to aliasKey_pub full_perm aliasKey_pub1);
            with aliasKey_priv1. assert (A.pts_to aliasKey_priv full_perm aliasKey_priv1);
            with deviceIDCSR1. assert (A.pts_to deviceIDCSR full_perm deviceIDCSR1);
            with aliasKeyCRT1. assert (A.pts_to aliasKeyCRT full_perm aliasKeyCRT1);
            let new_locked_context = init_l1_ctxt 
              deviceIDCSR_len aliasKeyCRT_len deviceID_priv deviceID_pub
              aliasKey_priv aliasKey_pub deviceIDCSR aliasKeyCRT
              #deviceID_priv1 #deviceID_pub1 #aliasKey_priv1 #aliasKey_pub1
              #deviceIDCSR1 #aliasKeyCRT1 #(hide r.deviceID_label_len)
              #(hide r.aliasKey_label_len) #s #r0 #(hide idcsr_ing) #(hide akcrt_ing) ();
            
            A.free deviceID_pub;
            A.free deviceID_priv;
            A.free aliasKey_pub;
            A.free aliasKey_priv;
            A.free deviceIDCSR;
            A.free aliasKeyCRT;
            
            let d = HT.delete #cht_sig #cpht locked_cht._1 ctxt_hndl;
            with x y. unfold (maybe_update d cht_sig locked_cht._1 x y);
            if d {
              assert (models cht_sig locked_cht._1 (PHT.delete cpht ctxt_hndl));
              let b = not_full #cht_sig #(PHT.delete cpht ctxt_hndl) locked_cht._1;
              if b {
                let i = HT.insert #cht_sig #(PHT.delete cpht ctxt_hndl) locked_cht._1 new_ctxt_hndl new_locked_context;
                with x y. unfold (maybe_update i cht_sig locked_cht._1 x y);
                if i {
                  assert (models cht_sig locked_cht._1 (PHT.insert (PHT.delete cpht ctxt_hndl) new_ctxt_hndl new_locked_context));
                  rewrite (l0_record_perm r r0) as (record_perm record repr);
                  L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
                  L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
                  Some new_ctxt_hndl
                } else {
                  // ERROR - insert failed
                  assert (models cht_sig locked_cht._1 (PHT.delete cpht ctxt_hndl));
                  rewrite (l0_record_perm r r0) as (record_perm record repr);
                  L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
                  L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
                  None #ctxt_hndl_t
              }} else {
                // ERROR - table full
                rewrite (l0_record_perm r r0) as (record_perm record repr);
                L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
                L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
                None #ctxt_hndl_t
            }} else {
              // ERROR - delete failed
              assert (models cht_sig locked_cht._1 cpht);
              rewrite (l0_record_perm r r0) as (record_perm record repr);
              L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
              L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
              None #ctxt_hndl_t
            }}
          _ -> {
            // ERROR - record should have type (L0_record r)
            fold (l0_context_perm c cr);
            rewrite (l0_context_perm c cr) as (context_perm ctxt ctxt_repr);
            destroy_ctxt ctxt;
            L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
            L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
            None #ctxt_hndl_t
          }}
        }
        _ -> { 
          // ERROR - cannot invoke DeriveChild with L1 context
          L.release #(context_perm ctxt ctxt_repr) ctxt_lk;
          L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
          L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
          None #ctxt_hndl_t
        }}}
        None -> { 
        // ERROR - bad context handle
        L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
        L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
        None #ctxt_hndl_t
        }}
      } else {
        // ERROR - lookup failed
        L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
        L.release #(exists_ (fun pht -> models cht_sig locked_cht._1 pht)) cht_lk;
        None #ctxt_hndl_t
      }}
    None -> { 
    // ERROR - bad session ID
    L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
    None #ctxt_hndl_t
    }}
  } else {
    // ERROR - lookup failed
    L.release #(exists_ (fun pht -> models sht_sig locked_sht._1 pht)) sht_lk;
    None #ctxt_hndl_t
  }
}
```
let derive_child = derive_child'