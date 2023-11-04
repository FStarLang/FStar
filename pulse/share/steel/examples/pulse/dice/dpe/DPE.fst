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
open Pulse.Lib.BoundedIntegers
open Pulse.Lib.OnRange

assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a

(* Global State *)

let ctxt_hndl_t = U32.t
let sid_t = U32.t
noeq
type session_state =
  | SessionStart
  | Available { handle:ctxt_hndl_t; context:context_t }
  | InUse

let session_state_perm (s:session_state) =
  match s with
  | SessionStart
  | InUse -> emp
  | Available { handle; context } ->
    exists_ (fun repr -> context_perm context repr)

let session_table_map = PHT.pht_t sid_t session_state

let session_perm (stm:session_table_map) (sid:nat) =
  if not(UInt.fits sid 32) then emp
  else let sid = U32.uint_to_t sid in
       match PHT.lookup stm sid with
       | None -> emp
       | Some s -> session_state_perm s

let global_state_lock_pred
  (session_id_counter: R.ref sid_t)
  (session_table: ht_t sid_t session_state)
: vprop
= exists_ (fun stm ->
  exists_ (fun sid ->
    pts_to session_id_counter sid **
    models session_table stm **
    on_range (session_perm stm) 0 (U32.v sid)))
  
noeq
type global_state_t = {
  session_id_counter: R.ref sid_t;
  session_table: ht_t sid_t session_state;
  lock: L.lock (global_state_lock_pred session_id_counter session_table)
}
let mk_global_state
      (sid_counter:R.ref sid_t)
      (session_table:ht_t sid_t session_state)
      (lock:L.lock (global_state_lock_pred sid_counter session_table))
: global_state_t
= { session_id_counter = sid_counter;
    session_table = session_table;
    lock = lock }

assume Fits_size_t_u32 : squash (US.fits_u32)
let sid_hash (x:sid_t) : US.t = US.of_u32 x

#push-options "--ext 'pulse:env_on_err' --print_implicits"
```pulse
fn alloc_global_state (_:unit)
  requires emp
  returns _:global_state_t
  ensures emp
{
  let sid_counter = R.alloc #sid_t 0ul;
  let session_table = HT.alloc #sid_t #session_state sid_hash 256sz;
  with stm. assert (models session_table stm);
  Pulse.Lib.OnRange.on_range_empty #emp_inames (session_perm stm) 0;
  fold (global_state_lock_pred sid_counter session_table);
  let lock = L.new_lock (global_state_lock_pred sid_counter session_table);
  mk_global_state sid_counter session_table lock
}
```
let global_state : global_state_t = run_stt (alloc_global_state ())

(* Utilities to work with on_range (session_perm stm) *)
(* <utilities on on_range> *)
let session_table_eq_on_range  
  (stm0 stm1:session_table_map)
  (i j:nat)
: prop
= forall (k:sid_t). i <= U32.v k && U32.v k < j ==> PHT.lookup stm0 k == PHT.lookup stm1 k

```pulse
ghost
fn frame_session_perm_at_sid 
    (stm0 stm1:session_table_map)
    (i j:nat)
    (_:squash (session_table_eq_on_range stm0 stm1 i j))
    (sid:(sid:nat { i <= sid /\ sid < j }))
  requires
    session_perm stm0 sid
  ensures
    session_perm stm1 sid
{
  rewrite (session_perm stm0 sid)
      as  (session_perm stm1 sid)
}
```

```pulse
ghost
fn frame_session_perm_on_range
    (stm0 stm1:session_table_map)
    (i j:nat)
  requires
    on_range (session_perm stm0) i j **
    pure (session_table_eq_on_range stm0 stm1 i j)
  ensures
    on_range (session_perm stm1) i j
{
  Pulse.Lib.OnRange.on_range_weaken #emp_inames
    (session_perm stm0)
    (session_perm stm1)
    i j
    (frame_session_perm_at_sid stm0 stm1 i j ())
}
```
(* </utilities on on_range> *)



(* ----------- IMPLEMENTATION ----------- *)

let coerce_us (x:pos_us) : SZ.t = x

(*
  GetProfile: Part of DPE API 
  Get the DPE's profile. 
*)
```pulse
fn get_profile' (_:unit)
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
let get_profile = get_profile'


```pulse
fn insert (#kt:eqtype) (#vt:Type0)
          (ht:ht_t kt vt) (k:kt) (v:vt)
          (#pht:erased (PHT.pht_t kt vt))
  requires
    models ht pht
  returns b:bool
  ensures
    exists pht'.
      models ht pht' **
      pure (if b
            then (PHT.not_full (reveal pht).repr /\
                  pht'==PHT.insert pht k v)
            else pht'==pht)
{
  let b = not_full ht;
  if b
  {
    Pulse.Lib.HashTable.insert ht k v;
  }
  else
  {
    false
  }
}
```

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
  L.acquire global_state.lock;
  unfold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  with pht0. assert (models global_state.session_table pht0);
  with i j. assert (on_range (session_perm pht0) i j);
  let sid = !global_state.session_id_counter;
  assert pure (U32.v sid == j);
  let opt_inc = sid `safe_add` 1ul;
  match opt_inc
  {
    None -> 
    {
      fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
      L.release global_state.lock;
      None #sid_t
    }
    Some next_sid ->
    {
      let r = insert global_state.session_table sid SessionStart;
      if r 
      {
        global_state.session_id_counter := next_sid;
        with pht1. assert (models global_state.session_table pht1);
        frame_session_perm_on_range pht0 pht1 i j;
        rewrite emp as (session_perm pht1 j);
        Pulse.Lib.OnRange.on_range_snoc #emp_inames () #(session_perm pht1);
        fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
        L.release global_state.lock;
        Some sid
      } 
      else
      {
        with pht1. rewrite (models global_state.session_table pht1)
                        as (models global_state.session_table pht0);    
        // ERROR - insert failed
        fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
        L.release global_state.lock;
        None #sid_t
      }
    }
  }
}
```
let open_session = open_session'

assume val dbg : vprop

let uds_of_engine_context_repr (r:_{Engine_context_repr? r}) : erased (Seq.seq U8.t)=
  match r with
  | Engine_context_repr uds_bytes -> uds_bytes


```pulse 
fn destroy_ctxt (ctxt:context_t) (#repr:erased context_repr_t)
  requires context_perm ctxt repr
  ensures emp
{
  match ctxt
  {
    Engine_context c ->
    {
      rewrite each ctxt as (Engine_context c);
      let uds = get_engine_context_perm c repr;
      unfold (engine_context_perm c uds);
      A.zeroize uds_len c.uds;
      A.free c.uds;
    }
    L0_context c ->
    {
      rewrite each ctxt as (L0_context c);
      let r = get_l0_context_perm c repr;
      unfold (l0_context_perm c r);
      with s. assert (A.pts_to c.cdi s);
      A.zeroize dice_digest_len c.cdi;
      A.free c.cdi;
    }
    L1_context c ->
    {
      rewrite each ctxt as (L1_context c);
      let r = get_l1_context_perm c repr;
      unfold (l1_context_perm c r);
      A.free c.deviceID_priv;
      A.free c.deviceID_pub;
      A.free c.aliasKey_priv;
      A.free c.aliasKey_pub;
      A.free c.aliasKeyCRT;
      A.free c.deviceIDCSR;
    }
  }
}
```

let opt #a (p:a -> vprop) (x:option a) : vprop =
  match x with
  | None -> emp
  | Some x -> p x

let available_session_state_perm (s:session_state) =
  session_state_perm s ** pure (Available? s)

```pulse
fn return_none (a:Type0) (#p:(a -> vprop))
  requires emp
  returns o:option a
  ensures opt p o
{
  rewrite emp as (opt p (None #a));
  None #a
}
```

let dflt #a (x:option a) (y:a) =
  match x with
  | Some v -> v
  | _ -> y

```pulse
fn take_session_state (sid:sid_t) (replace:session_state)
   requires session_state_perm replace
   returns r:option session_state
   ensures session_state_perm (dflt r replace)
  {
    L.acquire global_state.lock;
    unfold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
    let max_sid = !global_state.session_id_counter;
    if U32.(sid < max_sid)
    {
      with stm. assert (on_range (session_perm stm) 0 (U32.v max_sid));
      assert (models global_state.session_table stm);
      let ss = HT.lookup global_state.session_table sid;
      assert (models global_state.session_table stm);
      if fst ss
      {
        match snd ss 
        {
          Some st ->
          {
            let ok = insert global_state.session_table sid replace;
            if ok
            {
              Pulse.Lib.OnRange.on_range_get #emp_inames (U32.v sid);
              rewrite (session_perm stm (U32.v sid))
                   as (session_state_perm st);
              with stm'. assert (models global_state.session_table stm');
              frame_session_perm_on_range stm stm' 0 (U32.v sid);
              // with stm0. assert (on_range (session_perm stm0) 
              //                             (U32.v sid `Prims.op_Addition` 1)
              //                             (U32.v max_sid));
              frame_session_perm_on_range stm stm' (U32.v sid `Prims.op_Addition` 1) (U32.v max_sid);
              rewrite (session_state_perm replace)
                  as  (session_perm stm' (U32.v sid));
              Pulse.Lib.OnRange.on_range_put #emp_inames 
                    0 (U32.v sid) (U32.v max_sid)
                    #(session_perm stm');
              fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
              L.release global_state.lock;
              Some st
            }
            else
            {
              assert (models global_state.session_table stm);
              fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
              L.release global_state.lock;
              None #session_state
              // return_none session_state #(session_state_perm)
            }
          }

          None -> 
          {
            fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
            L.release global_state.lock;
            None #session_state
            // return_none session_state #(session_state_perm)
          }
        }
      }
      else 
      {
        fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
        L.release global_state.lock;
        None #session_state
        // return_none session_state #(session_state_perm)
      }
    }
    else
    {
      fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
      L.release global_state.lock;
      None #session_state
      // return_none session_state #(session_state_perm)
    }
  }
  ```

// ```pulse 
// fn destroy_locked_ctxt (locked_ctxt:locked_context_t)
//   requires emp
//   ensures emp
// {
//   let ctxt = locked_ctxt._1;
//   let repr = locked_ctxt._2;
//   let ctxt_lk = locked_ctxt._3;
//   // TODO: would be nice to use a rename here, to transfer ownership to ctxt_lk
//   L.acquire locked_ctxt._3;
//   destroy_ctxt locked_ctxt._1;
// }
// ```

let ctxt_of (s:session_state { Available? s })
  : context_t
  = let Available { context } = s in context

```pulse
ghost
fn elim_session_state_perm_available (s:(s:session_state { Available? s }))
  requires session_state_perm s 
  ensures exists r. context_perm (ctxt_of s) r 
{
  match s
  {
    Available ctxt ->
    {
      unfold (session_state_perm s);
      admit()
    }
  }
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
  rewrite emp as (session_state_perm SessionStart);
  let st = take_session_state sid SessionStart;
  match st
  {
    None ->
    {
      with s. rewrite (session_state_perm s) as emp;
      false
    }

  
    Some st ->
    {
      with s. rewrite (session_state_perm s)
                   as (session_state_perm st);
      match st
      {
        Available ctxt ->
        {
          elim_session_state_perm_available st;
          destroy_ctxt (ctxt_of st);
          true
        }

        SessionStart ->
        {
          rewrite (session_state_perm st) as emp;
          false
        }

        InUse -> 
        {
          rewrite (session_state_perm st) as emp;
          false
        }

      }
    }
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
  rewrite each locked_sht._2 as sht_lk;
  L.acquire sht_lk;
  let res = HT.lookup locked_sht._1 sid;
  if (fst res) 
  {
    let opt_locked_cht = snd res;
    match opt_locked_cht
    {
      Some locked_cht ->
      { 
        let cht_lk = locked_cht._2;
        rewrite each locked_cht._2 as cht_lk;
        // Note: We don't release this lock because we give up permission
        // on the cht when we deallocate it
        L.acquire cht_lk; 
        dealloc locked_cht._1;//TODO: destroy locked ctxt cht_len;// destroy_locked_ctxt;
        let b = HT.delete locked_sht._1 sid;
        if b
        {
          L.release sht_lk;
          b
        } else {
          L.release sht_lk;
          b
        }
      }
      None ->
      {
        // ERROR - bad session ID
        L.release sht_lk;
        false
      }
    }
  } 
  else
  {
    // ERROR - lookup failed
    L.release sht_lk;
    false
  }
}
```
let close_session = close_session'

// TODO: 
let prng (_:unit) : U32.t = admit()

```pulse
fn init_engine_ctxt (uds:A.larray U8.t (US.v uds_len))
                    (#p:perm)
                    (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  requires A.pts_to uds #p uds_bytes
        ** uds_is_enabled
  returns _:locked_context_t
  ensures A.pts_to uds #p uds_bytes
{
  let uds_buf = A.alloc 0uy uds_len;
  memcpy uds_len uds uds_buf;
  disable_uds ();
  let engine_context = mk_engine_context_t uds_buf;

  rewrite each uds_buf as (engine_context.uds);
  fold (engine_context_perm engine_context uds_bytes);

  let ctxt = mk_context_t_engine engine_context;
  rewrite (engine_context_perm engine_context uds_bytes) 
    as (context_perm ctxt (Engine_context_repr uds_bytes));

  let ctxt_lk = L.new_lock (context_perm ctxt (Engine_context_repr uds_bytes));
  ((| ctxt, hide (Engine_context_repr uds_bytes), ctxt_lk |) <: locked_context_t)
}
```

```pulse
fn init_l0_ctxt (cdi:A.larray U8.t (US.v dice_digest_len))  
                (#engine_repr:erased engine_record_repr)
                (#s:erased (Seq.seq U8.t))
                (#uds_bytes:erased (Seq.seq U8.t))
                (_:squash(cdi_functional_correctness s uds_bytes engine_repr
                      /\ l0_is_authentic engine_repr))
  requires A.pts_to cdi s
        ** pure (A.is_full_array cdi)
  returns _:locked_context_t
  ensures emp
{
  let cdi_buf = A.alloc 0uy dice_digest_len;
  memcpy dice_digest_len cdi cdi_buf;
  A.zeroize dice_digest_len cdi;
  A.free cdi;

  let l0_context = mk_l0_context_t cdi_buf;
  let l0_context_repr = hide (mk_l0_context_repr_t uds_bytes s engine_repr);
  rewrite each cdi_buf as (l0_context.cdi);
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
                (#deviceID_priv0 #deviceID_pub0 #aliasKey_priv0 #aliasKey_pub0
                 #deviceIDCSR0 #aliasKeyCRT0:erased (Seq.seq U8.t))
                (#deviceID_label_len #aliasKey_label_len: erased hkdf_lbl_len)
                (#cdi:erased (Seq.seq U8.t))
                (#repr:erased l0_record_repr_t)
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
  requires A.pts_to deviceID_priv deviceID_priv0 ** 
           A.pts_to deviceID_pub deviceID_pub0 ** 
           A.pts_to aliasKey_priv aliasKey_priv0 ** 
           A.pts_to aliasKey_pub aliasKey_pub0 ** 
           A.pts_to deviceIDCSR deviceIDCSR0 **
           A.pts_to aliasKeyCRT aliasKeyCRT0
  returns _:locked_context_t
  ensures 
    A.pts_to deviceID_priv deviceID_priv0 ** 
    A.pts_to deviceID_pub deviceID_pub0 **
    A.pts_to aliasKey_priv aliasKey_priv0 ** 
    A.pts_to aliasKey_pub aliasKey_pub0 ** 
    A.pts_to deviceIDCSR deviceIDCSR0 **
    A.pts_to aliasKeyCRT aliasKeyCRT0
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

  let ctxt = mk_context_t_l1 l1_context;
  let repr = mk_context_repr_t_l1 l1_context_repr;
  rewrite (l1_context_perm l1_context l1_context_repr) as (context_perm ctxt repr);
  
  let ctxt_lk = L.new_lock (context_perm ctxt repr);
  (| ctxt, repr, ctxt_lk |)
}
```

(*
  InitializeContext: Part of DPE API 
  Create a context in the initial state (engine context) and store the context
  in the current session's context table. Return the context handle upon
  success and None upon failure. 
*)
```pulse
fn initialize_context' (sid:sid_t) (uds:A.larray U8.t (US.v uds_len)) 
                       (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  requires A.pts_to uds #p uds_bytes
        ** uds_is_enabled
  returns _:option ctxt_hndl_t
  ensures A.pts_to uds #p uds_bytes
{
  let locked_context = init_engine_ctxt uds;
  let ctxt_hndl = prng ();

  let sht_lk = locked_sht._2;
  rewrite each locked_sht._2 as sht_lk;
  L.acquire sht_lk;

  let res = HT.lookup locked_sht._1 sid;
  if (fst res)
  {
    let opt_locked_cht = snd res;
    match opt_locked_cht
    {
      Some locked_cht ->
      {
        let cht_lk = locked_cht._2;
        rewrite each locked_cht._2 as cht_lk;
        L.acquire cht_lk;

        let b = not_full locked_cht._1;
        if b
        {
          let r = HT.insert locked_cht._1 ctxt_hndl locked_context;
          if r
          {
            L.release sht_lk;
            L.release cht_lk;
            Some ctxt_hndl
          }
          else
          {
            // ERROR - insert failed
            L.release sht_lk;
            L.release cht_lk;
            None #ctxt_hndl_t     
          }
        }
        else
        {
          // ERROR - table full
          L.release sht_lk;
          L.release cht_lk;
          None #ctxt_hndl_t
        }
      }
      None -> {
        // ERROR - bad session ID
        L.release sht_lk;
        None #ctxt_hndl_t
      }
    }
  }
  else
  {
    // ERROR - lookup failed
    L.release sht_lk;
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
  rewrite each locked_sht._2 as sht_lk;
  L.acquire sht_lk;

  let res = HT.lookup locked_sht._1 sid;
  if (fst res)
  {
    let opt_locked_cht = snd res;
    match opt_locked_cht
    {
      Some locked_cht ->
      {
        let cht_lk = locked_cht._2;
        rewrite each locked_cht._2 as cht_lk;
        L.acquire cht_lk;
        let r = HT.lookup locked_cht._1 ctxt_hndl;
        if (fst r)
        {
          let opt_locked_ctxt = snd r;
          match opt_locked_ctxt
          {
            Some locked_context ->
            {
              let b = not_full locked_cht._1;
              if b
              {
                let r = HT.insert locked_cht._1 new_ctxt_hndl locked_context;
                if r
                {
                  let d = HT.delete locked_cht._1 ctxt_hndl;
                  if d
                  {
                    L.release sht_lk;
                    L.release cht_lk;
                    Some new_ctxt_hndl
                  }
                  else
                  {
                    // ERROR - delete failed
                    L.release sht_lk;
                    L.release cht_lk;
                    None #ctxt_hndl_t
                  }
                } 
                else 
                {
                  // ERROR - insert failed
                  L.release sht_lk;
                  L.release cht_lk;
                  None #ctxt_hndl_t
                }
              }
              else
              {
                  // ERROR - table full
                  L.release sht_lk;
                  L.release cht_lk;
                  None #ctxt_hndl_t
              }
            }
            None ->
            {
              // ERROR - bad context handle
              L.release sht_lk;
              L.release cht_lk;
              None #ctxt_hndl_t 
            }
          }
        }
        else
        {
          // ERROR - lookup failed
          L.release sht_lk;
          L.release cht_lk;
          None #ctxt_hndl_t 
        }
      }
      None ->
      {
        // ERROR - lookup context table failed
        L.release sht_lk;
        None #ctxt_hndl_t 
      }
    }
  }
  else
  {
    // ERROR - lookup context table failed
    L.release sht_lk;
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
fn derive_child' (sid:sid_t) (ctxt_hndl:ctxt_hndl_t) (record:record_t)
                 (#repr:erased repr_t) (#p:perm)
  requires record_perm record p repr
  returns _:option ctxt_hndl_t
  ensures record_perm record p repr
{
  let new_ctxt_hndl = prng ();

  let sht_lk = locked_sht._2;
  rewrite each locked_sht._2 as sht_lk;
  L.acquire sht_lk;
  // with spht. assert (models sht_sig locked_sht._1 spht);

  let res = HT.lookup locked_sht._1 sid;
  if (fst res)
  {
    let opt_locked_cht = snd res;
    match opt_locked_cht
    {
      Some locked_cht ->
      {
        let cht_lk = locked_cht._2;
        rewrite each locked_cht._2 as cht_lk;
        L.acquire cht_lk;
        with cpht. assert (models locked_cht._1 cpht);

        let r = HT.lookup locked_cht._1 ctxt_hndl;
        if (fst r)
        {
          let opt_locked_ctxt = snd r;
          match opt_locked_ctxt
          {
            Some locked_ctxt ->
            {
              let ctxt = locked_ctxt._1;
              let ctxt_repr = locked_ctxt._2;
              let ctxt_lk = locked_ctxt._3;
              L.acquire #(context_perm ctxt ctxt_repr) ctxt_lk;
              
              match ctxt
              {
                Engine_context c ->
                {
                  // NOTE: we won't eventually release engine_context_perm because we won't 
                  // own it anymore -- we will free the uds array
                  rewrite each ctxt as (Engine_context c);
                  let uds = get_engine_context_perm c ctxt_repr;
                  // rewrite (context_perm (E) ctxt_repr) as (engine_context_perm c);
                  unfold (engine_context_perm c uds);
                  match record
                  {
                    Engine_record r ->
                    {
                      rewrite each record as (Engine_record r);
                      let r0 = get_engine_record_perm r repr p;
                      
                      let cdi = A.alloc 0uy dice_digest_len;
                      let ret = EngineCore.engine_main cdi c.uds r;
                      with s. assert (A.pts_to cdi s);
                      fold (engine_context_perm c uds);
                      rewrite (engine_context_perm c uds)
                           as (context_perm ctxt ctxt_repr);
                      destroy_ctxt ctxt;

                      match ret
                      {
                        DICE_SUCCESS ->
                        {
                          let new_locked_context = init_l0_ctxt cdi #r0 #s #uds ();
                          
                          let d = HT.delete locked_cht._1 ctxt_hndl;
                          if d 
                          {
                            let b = not_full locked_cht._1;
                            if b
                            {
                              let i = HT.insert locked_cht._1 new_ctxt_hndl new_locked_context; 
                              // with x y. unfold (maybe_update i cht_sig locked_cht._1 x y);
                              if i 
                              {
                                // assert (models cht_sig locked_cht._1 (PHT.insert (PHT.delete cpht ctxt_hndl) new_ctxt_hndl new_locked_context));
                                rewrite (engine_record_perm r p r0)
                                     as (record_perm record p repr);
                                L.release sht_lk;
                                L.release cht_lk;
                                Some new_ctxt_hndl
                              } 
                              else
                              {
                                // ERROR - insert failed
                                // assert (models cht_sig locked_cht._1 (PHT.delete cpht ctxt_hndl));
                                rewrite (engine_record_perm r p r0)
                                     as (record_perm record p repr);
                                L.release sht_lk;
                                L.release cht_lk;
                                None #ctxt_hndl_t
                              }
                            } 
                            else
                            {
                                          // ERROR - table full
                                rewrite (engine_record_perm r p r0)
                                     as (record_perm record p repr);
                                L.release sht_lk;
                                L.release cht_lk;
                                None #ctxt_hndl_t
                            }
                          } 
                          else
                          {
                            // ERROR - delete failed
                            // assert (models cht_sig locked_cht._1 cpht);
                            rewrite (engine_record_perm r p r0)
                                 as (record_perm record p repr);
                            L.release sht_lk;
                            L.release cht_lk;
                            None #ctxt_hndl_t
                          }
                        }
                        DICE_ERROR ->
                        {
                          // ERROR - DICE engine failed
                          A.zeroize dice_digest_len cdi;
                          A.free cdi;
                          rewrite (engine_record_perm r p r0)
                               as (record_perm record p repr);
                          L.release sht_lk;
                          L.release cht_lk;
                          None #ctxt_hndl_t
                        }
                      }
                    }
                    _ ->
                    { 
                      // ERROR - record should have type (Engine_record r)
                      // TODO: prove this case is unreachable
                      fold (engine_context_perm c uds);
                      rewrite (engine_context_perm c uds)
                           as (context_perm ctxt ctxt_repr);
                      destroy_ctxt ctxt;
                      L.release sht_lk;
                      L.release cht_lk;
                      None #ctxt_hndl_t
                    }
                  }
                }
                L0_context c ->
                { 
                  // NOTE: we won't eventually release l0_context_perm because we won't 
                  // own it anymore -- we will free the cdi array
                  rewrite each ctxt as (L0_context c);
                  let cr = get_l0_context_perm c ctxt_repr;
                  unfold (l0_context_perm c cr);
                  with s. assert (A.pts_to c.cdi s);

                  match record
                  {
                    L0_record r ->
                    {
                      rewrite each record as (L0_record r);
                      let r0 = get_l0_record_perm r repr p;

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

                      with deviceID_pub1. assert (A.pts_to deviceID_pub deviceID_pub1);
                      with deviceID_priv1. assert (A.pts_to deviceID_priv deviceID_priv1);
                      with aliasKey_pub1. assert (A.pts_to aliasKey_pub aliasKey_pub1);
                      with aliasKey_priv1. assert (A.pts_to aliasKey_priv aliasKey_priv1);
                      with deviceIDCSR1. assert (A.pts_to deviceIDCSR deviceIDCSR1);
                      with aliasKeyCRT1. assert (A.pts_to aliasKeyCRT aliasKeyCRT1);
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
                      
                      let d = HT.delete locked_cht._1 ctxt_hndl;
                      // with x y. unfold (maybe_update d cht_sig locked_cht._1 x y);
                      if d
                      {
                        // assert (models cht_sig locked_cht._1 (PHT.delete cpht ctxt_hndl));
                        let b = not_full locked_cht._1;
                        if b
                        {
                          let i = HT.insert locked_cht._1 new_ctxt_hndl new_locked_context;
                          // with x y. unfold (maybe_update i cht_sig locked_cht._1 x y);
                          if i
                          {
                            // assert (models cht_sig locked_cht._1 (PHT.insert (PHT.delete cpht ctxt_hndl) new_ctxt_hndl new_locked_context));
                            rewrite (l0_record_perm r p r0)
                                 as (record_perm record p repr);
                            L.release  sht_lk;
                            L.release  cht_lk;
                            Some new_ctxt_hndl
                          }
                          else
                          {
                            // ERROR - insert failed
                            // assert (models cht_sig locked_cht._1 (PHT.delete cpht ctxt_hndl));
                            rewrite (l0_record_perm r p r0)
                                 as (record_perm record p repr);
                            L.release  sht_lk;
                            L.release  cht_lk;
                            None #ctxt_hndl_t
                          }
                        }
                        else
                        {
                          // ERROR - table full
                          rewrite (l0_record_perm r p r0)
                              as (record_perm record p repr);
                          L.release  sht_lk;
                          L.release  cht_lk;
                          None #ctxt_hndl_t
                        }
                      }
                      else
                      {
                        // ERROR - delete failed
                        // assert (models cht_sig locked_cht._1 cpht);
                        rewrite (l0_record_perm r p r0)
                             as (record_perm record p repr);
                        L.release  sht_lk;
                        L.release  cht_lk;
                        None #ctxt_hndl_t
                      }
                    }
                    _ ->
                    {
                      // ERROR - record should have type (L0_record r)
                      fold (l0_context_perm c cr);
                      rewrite (l0_context_perm c cr)
                           as (context_perm ctxt ctxt_repr);
                      destroy_ctxt ctxt;
                      L.release  sht_lk;
                      L.release  cht_lk;
                      None #ctxt_hndl_t
                    }
                  }
                }
                _ ->
                { 
                  // ERROR - cannot invoke DeriveChild with L1 context
                  L.release #(context_perm ctxt ctxt_repr) ctxt_lk;
                  L.release  sht_lk;
                  L.release  cht_lk;
                  None #ctxt_hndl_t
                }
              }
            }
            None ->
            { 
              // ERROR - bad context handle
              L.release  sht_lk;
              L.release  cht_lk;
              None #ctxt_hndl_t
            }
          }
        } 
        else
        {
          // ERROR - lookup failed
          L.release  sht_lk;
          L.release  cht_lk;
          None #ctxt_hndl_t
        }
      }
      None ->
      { 
        // ERROR - bad session ID
        L.release  sht_lk;
        None #ctxt_hndl_t
      }
    }
  }
  else
  {
    // ERROR - lookup failed
    L.release  sht_lk;
    None #ctxt_hndl_t
  }
}
```
let derive_child = derive_child'