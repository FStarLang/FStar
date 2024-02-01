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
open Pulse.Lib.Mutex

assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a

(* Global State *)

let ctxt_hndl_t = U32.t

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

let session_state_perm (s:session_state) =
  match s with
  | SessionStart
  | InUse
  | SessionClosed
  | SessionError -> emp
  | Available _ ->
    exists* repr. context_perm (ctxt_of s) repr

let mk_available_payload handle context = { handle; context }

```pulse
fn intro_session_state_perm_available 
      (ctxt:context_t)
      (hndl:ctxt_hndl_t)
  requires context_perm ctxt 'repr
  returns s:session_state
  ensures session_state_perm s
{
  rewrite (context_perm ctxt 'repr)
       as (context_perm (ctxt_of (Available (mk_available_payload hndl ctxt))) 'repr);
  fold (session_state_perm (Available (mk_available_payload hndl ctxt)));
  Available (mk_available_payload hndl ctxt)
}
```

```pulse
ghost
fn elim_session_state_perm_available (s:(s:session_state { Available? s }))
  requires session_state_perm s 
  ensures exists* r. context_perm (ctxt_of s) r 
{
  match s
  {
    Available ctxt ->
    {
      rewrite (session_state_perm s) as (session_state_perm (Available ctxt));
      unfold (session_state_perm (Available ctxt));
      with x y. rewrite (context_perm x y) as (context_perm (ctxt_of s) y);
    }
  }
}
```

// Marking this noextract since this spec only
// What will krml do?
noextract
let session_table_map = PHT.pht_t sid_t session_state

let session_perm (stm:session_table_map) (sid:nat) =
  if not(UInt.fits sid 32) then emp
  else let sid = U32.uint_to_t sid in
       match PHT.lookup stm sid with
       | None -> emp
       | Some s -> session_state_perm s

noeq
type global_state_t = {
  session_id_counter:sid_t;
  session_table:ht_t sid_t session_state;
}

let global_state_mutex_pred (gst:option global_state_t) : vprop =
  match gst with
  | None -> emp
  | Some gst ->
    exists* stm.
      models gst.session_table stm **
      on_range (session_perm stm) 0 (U32.v gst.session_id_counter)


// assume Fits_size_t_u32 : squash (US.fits_u32)
// let sid_hash (x:sid_t) : US.t = US.of_u32 x

assume val sid_hash : sid_t -> US.t  // TODO


// TODO: mark this as const for Rust extraction

```pulse
fn initialize_global_state ()
  requires emp
  returns m:mutex global_state_mutex_pred
  ensures emp
{
  let res = None #global_state_t;
  rewrite emp as (global_state_mutex_pred res);
  new_mutex global_state_mutex_pred res
}
```

let global_state : mutex global_state_mutex_pred = run_stt (initialize_global_state ())

```pulse
fn mk_global_state ()
  requires emp
  returns st:global_state_t
  ensures global_state_mutex_pred (Some st)
{
  let session_table = HT.alloc #sid_t #session_state sid_hash 256sz;
  let st = {
    session_id_counter = 0ul;
    session_table;
  };
  with pht. assert (models session_table pht);
  rewrite (models session_table pht) as (models st.session_table pht);
  Pulse.Lib.OnRange.on_range_empty #emp_inames (session_perm pht) 0;
  fold (global_state_mutex_pred (Some st));
  st
}
```

#push-options "--ext 'pulse:env_on_err' --print_implicits --warn_error -342"


(* Utilities to work with on_range (session_perm stm) *)
(* <utilities on on_range> *)
noextract  // TODO: why do we extract this at all, it is a prop
let session_table_eq_on_range
  (stm0 stm1:session_table_map)
  (i j:nat)
  : prop =
  forall (k:sid_t). i <= U32.v k && U32.v k < j ==> PHT.lookup stm0 k == PHT.lookup stm1 k

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

(*
  GetProfile: Part of DPE API 
  Get the DPE's profile. 
*)
```pulse
fn get_profile' ()
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


//
// Wrapper over hash table insert that first checks if the table is full
//

```pulse
fn insert_if_not_full (#kt:eqtype) (#vt:Type0)
  (ht:ht_t kt vt) (k:kt) (v:vt)
  (#pht:erased (PHT.pht_t kt vt))
  requires models ht pht
  returns b:(ht_t kt vt & bool)
  ensures
    exists* pht'.
      models (fst b) pht' **
      pure (same_sz_and_hashf (fst b) ht /\
            (if snd b
            then (PHT.not_full (reveal pht).repr /\
                  pht'==PHT.insert pht k v)
            else pht'==pht))
{
  let b = not_full ht;
  if snd b
  {
    Pulse.Lib.HashTable.insert (fst b) k v
  }
  else
  {
    let res = (fst b, false);
    rewrite (models (fst b) pht) as (models (fst res) pht);
    res
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

assume val safe_add (i j:U32.t)
  : o:option U32.t { Some? o ==> U32.v (Some?.v o) == U32.v i + U32.v j }

#push-options "--z3rlimit_factor 4"
```pulse
fn open_session_aux (st:global_state_t)
  requires global_state_mutex_pred (Some st)
  returns b:(global_state_t & option sid_t)
  ensures global_state_mutex_pred (Some (fst b))
{
  unfold (global_state_mutex_pred (Some st));
  let ctr = st.session_id_counter;
  let tbl = st.session_table;
  with stm. rewrite (models st.session_table stm) as (models tbl stm);
  with stm. rewrite (on_range (session_perm stm) 0 (U32.v st.session_id_counter))
                 as (on_range (session_perm stm) 0 (U32.v ctr));

  with pht0. assert (models tbl pht0);
  with i j. assert (on_range (session_perm pht0) i j);
  assert (pure (U32.v ctr == j));

  let opt_inc = ctr `safe_add` 1ul;
  
  match opt_inc {
    None -> {
      admit ()
      // let st = { session_id_counter = ctr; session_table = tbl };
      // with stm. rewrite (models tbl stm) as (models st.session_table stm);
      // with stm. rewrite (on_range (session_perm stm) 0 (U32.v ctr))
      //                as (on_range (session_perm stm) 0 (U32.v st.session_id_counter));
      // fold (global_state_mutex_pred (Some st));
      // let res = (st, None #sid_t);
      // rewrite (global_state_mutex_pred (Some st)) as (global_state_mutex_pred (Some (fst res)));
      // res
    }
    Some next_sid -> {
      let res = insert_if_not_full tbl next_sid SessionStart;
      if snd res {
        let st = { session_id_counter = next_sid; session_table = fst res };
        with pht1. assert (models (fst res) pht1);
        rewrite (models (fst res) pht1) as (models st.session_table pht1);
        assert (pure (pht1 == PHT.insert pht0 next_sid SessionStart));
        frame_session_perm_on_range pht0 pht1 i j;
        // rewrite emp as (session_perm pht1 j);
        admit (session_perm pht1 j);
        Pulse.Lib.OnRange.on_range_snoc #emp_inames () #(session_perm pht1);
        admit ();

        (st, Some next_sid)
      } else {
        admit ()
        // let st = { session_id_counter = ctr; session_table = fst res };
        // with stm. rewrite (models (fst res) stm) as (models st.session_table stm);
        // with stm1. assert (models st.session_table stm1);
        // with stm. rewrite (on_range (session_perm stm) 0 (U32.v ctr))
        //                as (on_range (session_perm stm1) 0 (U32.v st.session_id_counter));
        // fold (global_state_mutex_pred (Some st));
        // let res = (st, None #sid_t);
        // rewrite (global_state_mutex_pred (Some st)) as (global_state_mutex_pred (Some (fst res)));
        // res
      }
    }
  }

  // with ht. assert (pts_to global_state.session_table ht);
  // with pht0. assert (models ht pht0);
  // with i j. assert (on_range (session_perm pht0) i j);
  // let sid = !global_state.session_id_counter;
  // assert pure (U32.v sid == j);
  // let opt_inc = sid `safe_add` 1ul;
  // match opt_inc
  // {
  //   None -> 
  //   {
  //     fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //     L.release global_state.lock;
  //     None #sid_t
  //   }
  //   Some next_sid ->
  //   {
  //     let r = insert global_state.session_table sid SessionStart;
  //     if r 
  //     {
  //       global_state.session_id_counter := next_sid;
  //       with pht1. assert (models ht pht1);
  //       frame_session_perm_on_range pht0 pht1 i j;
  //       rewrite emp as (session_perm pht1 j);
  //       Pulse.Lib.OnRange.on_range_snoc #emp_inames () #(session_perm pht1);
  //       fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //       L.release global_state.lock;
  //       Some sid
  //     } 
  //     else
  //     {
  //       with pht1. rewrite (models ht pht1)
  //                       as (models ht pht0);
  //       // ERROR - insert failed
  //       fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //       L.release global_state.lock;
  //       None #sid_t
  //     }
  //   }
  // } 
}
```
#pop-options

```pulse
fn open_session ()
  requires emp
  returns _:option sid_t
  ensures emp
{
  let r = lock global_state;
  let st_opt = R.replace r None;

  match st_opt {
    None -> {
      rewrite (global_state_mutex_pred None) as emp;
      let st = mk_global_state ();
      let res = open_session_aux st;
      r := Some (fst res);
      unlock global_state r;
      (snd res)
    }
    Some st -> {
      let res = open_session_aux st;
      r := Some (fst res);
      unlock global_state r;
      (snd res)
    }
  }

  // L.acquire global_state.lock;
  // unfold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  // with ht. assert (pts_to global_state.session_table ht);
  // with pht0. assert (models ht pht0);
  // with i j. assert (on_range (session_perm pht0) i j);
  // let sid = !global_state.session_id_counter;
  // assert pure (U32.v sid == j);
  // let opt_inc = sid `safe_add` 1ul;
  // match opt_inc
  // {
  //   None -> 
  //   {
  //     fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //     L.release global_state.lock;
  //     None #sid_t
  //   }
  //   Some next_sid ->
  //   {
  //     let r = insert global_state.session_table sid SessionStart;
  //     if r 
  //     {
  //       global_state.session_id_counter := next_sid;
  //       with pht1. assert (models ht pht1);
  //       frame_session_perm_on_range pht0 pht1 i j;
  //       rewrite emp as (session_perm pht1 j);
  //       Pulse.Lib.OnRange.on_range_snoc #emp_inames () #(session_perm pht1);
  //       fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //       L.release global_state.lock;
  //       Some sid
  //     } 
  //     else
  //     {
  //       with pht1. rewrite (models ht pht1)
  //                       as (models ht pht0);
  //       // ERROR - insert failed
  //       fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //       L.release global_state.lock;
  //       None #sid_t
  //     }
  //   }
  // }
}
```
// let open_session = open_session'

// assume val dbg : vprop

// let uds_of_engine_context_repr (r:_{Engine_context_repr? r}) : erased (Seq.seq U8.t)=
//   match r with
//   | Engine_context_repr uds_bytes -> uds_bytes

module V = Pulse.Lib.Vec

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
      // A.zeroize uds_len c.uds;
      V.free c.uds;
    }
    L0_context c ->
    {
      rewrite each ctxt as (L0_context c);
      let r = get_l0_context_perm c repr;
      unfold (l0_context_perm c r);
      // with s. assert (V.pts_to c.cdi s);
      // A.zeroize dice_digest_len c.cdi;
      V.free c.cdi;
    }
    L1_context c ->
    {
      rewrite each ctxt as (L1_context c);
      let r = get_l1_context_perm c repr;
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

let opt #a (p:a -> vprop) (x:option a) : vprop =
  match x with
  | None -> emp
  | Some x -> p x

// let available_session_state_perm (s:session_state) =
//   session_state_perm s ** pure (Available? s)

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

#push-options "--z3rlimit_factor 4"
```pulse
fn take_session_state (sid:sid_t) (replace_with:session_state)
   requires session_state_perm replace_with
   returns r:option session_state
   ensures session_state_perm (dflt r replace_with)
  {
    let r = lock global_state;
    let st_opt = R.replace r None;

    match st_opt {
      None -> {
        unlock global_state r;
        None #session_state
      }
      Some st -> {
        unfold (global_state_mutex_pred (Some st));
        let ctr = st.session_id_counter;
        let tbl = st.session_table;
        if UInt32.lt sid ctr {
          with stm. assert (models st.session_table stm);
          rewrite (models st.session_table stm) as (models tbl stm);
          assert (on_range (session_perm stm) 0 (U32.v st.session_id_counter));
          rewrite (on_range (session_perm stm) 0 (U32.v st.session_id_counter))
               as (on_range (session_perm stm) 0 (U32.v ctr));
          let ss = HT.lookup tbl sid;
          assert (models (tfst ss) stm);
          if tsnd ss {
            match tthd ss {
              Some idx -> {
                let ok = HT.replace #_ #_ #stm (tfst ss) idx sid replace_with ();
                Pulse.Lib.OnRange.on_range_get #emp_inames (U32.v sid);
                let st1 = { session_id_counter = ctr; session_table = fst ok };
                r := Some st1;
                admit ();
                unlock global_state r;
                Some (snd ok)
                // let ok = insert global_state.session_table sid replace;
                // if ok {
                //   Pulse.Lib.OnRange.on_range_get #emp_inames (U32.v sid);
                //   rewrite (session_perm stm (U32.v sid))
                //        as (session_state_perm st);
                //   with stm'. assert (models ht stm');
                //   frame_session_perm_on_range stm stm' 0 (U32.v sid);
                //   // with stm0. assert (on_range (session_perm stm0) 
                //   //                             (U32.v sid `Prims.op_Addition` 1)
                //   //                             (U32.v max_sid));
                //   frame_session_perm_on_range stm stm' (U32.v sid `Prims.op_Addition` 1) (U32.v max_sid);
                //   rewrite (session_state_perm replace)
                //       as  (session_perm stm' (U32.v sid));
                //   Pulse.Lib.OnRange.on_range_put #emp_inames 
                //         0 (U32.v sid) (U32.v max_sid)
                //         #(session_perm stm');
                //   fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
                //   L.release global_state.lock;
                //   Some st
                // } else {
                //   assert (models ht stm);
                //   fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
                //   L.release global_state.lock;
                //   None #session_state
                //   // return_none session_state #(session_state_perm)
                // }
              }
              None ->  {
                let st1 = { session_id_counter = ctr; session_table = tfst ss };
                rewrite (models (tfst ss) stm) as (models st1.session_table stm);
                rewrite (on_range (session_perm stm) 0 (U32.v ctr))
                     as (on_range (session_perm stm) 0 (U32.v st1.session_id_counter));
                fold (global_state_mutex_pred (Some st1));
                r := Some st1;
                unlock global_state r;
                None #session_state
              }
            }
          } else  {
            let st1 = { session_id_counter = ctr; session_table = tfst ss };
            rewrite (models (tfst ss) stm) as (models st1.session_table stm);
            rewrite (on_range (session_perm stm) 0 (U32.v ctr))
                 as (on_range (session_perm stm) 0 (U32.v st1.session_id_counter));
            fold (global_state_mutex_pred (Some st1));
            r := Some st1;
            unlock global_state r;
            None #session_state
          }
        } else {
          let st1 = { session_id_counter = ctr; session_table = tbl };
          with stm. rewrite (models st.session_table stm) as (models st1.session_table stm);
          with stm. rewrite (on_range (session_perm stm) 0 (U32.v st.session_id_counter))
                         as (on_range (session_perm stm) 0 (U32.v st1.session_id_counter));
          fold (global_state_mutex_pred (Some st1));
          r := Some st1;
          unlock global_state r;
          None #session_state
        }
      }
    }

  //   L.acquire global_state.lock;
  //   unfold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //   let max_sid = !global_state.session_id_counter;
  //   if U32.(sid < max_sid)
  //   {
  //     with stm. assert (on_range (session_perm stm) 0 (U32.v max_sid));
  //     with ht. assert (pts_to global_state.session_table ht);
  //     assert (models ht stm);
  //     let ss = HT.lookup global_state.session_table sid;
  //     assert (models ht stm);
  //     if fst ss
  //     {
  //       match snd ss 
  //       {
  //         Some st ->
  //         {
  //           let ok = insert global_state.session_table sid replace;
  //           if ok
  //           {
  //             Pulse.Lib.OnRange.on_range_get #emp_inames (U32.v sid);
  //             rewrite (session_perm stm (U32.v sid))
  //                  as (session_state_perm st);
  //             with stm'. assert (models ht stm');
  //             frame_session_perm_on_range stm stm' 0 (U32.v sid);
  //             // with stm0. assert (on_range (session_perm stm0) 
  //             //                             (U32.v sid `Prims.op_Addition` 1)
  //             //                             (U32.v max_sid));
  //             frame_session_perm_on_range stm stm' (U32.v sid `Prims.op_Addition` 1) (U32.v max_sid);
  //             rewrite (session_state_perm replace)
  //                 as  (session_perm stm' (U32.v sid));
  //             Pulse.Lib.OnRange.on_range_put #emp_inames 
  //                   0 (U32.v sid) (U32.v max_sid)
  //                   #(session_perm stm');
  //             fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //             L.release global_state.lock;
  //             Some st
  //           }
  //           else
  //           {
  //             assert (models ht stm);
  //             fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //             L.release global_state.lock;
  //             None #session_state
  //             // return_none session_state #(session_state_perm)
  //           }
  //         }

  //         None -> 
  //         {
  //           fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //           L.release global_state.lock;
  //           None #session_state
  //           // return_none session_state #(session_state_perm)
  //         }
  //       }
  //     }
  //     else 
  //     {
  //       fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //       L.release global_state.lock;
  //       None #session_state
  //       // return_none session_state #(session_state_perm)
  //     }
  //   }
  //   else
  //   {
  //     fold (global_state_lock_pred global_state.session_id_counter global_state.session_table);
  //     L.release global_state.lock;
  //     None #session_state
  //     // return_none session_state #(session_state_perm)
  //   }
  }
  ```

// // ```pulse 
// // fn destroy_locked_ctxt (locked_ctxt:locked_context_t)
// //   requires emp
// //   ensures emp
// // {
// //   let ctxt = locked_ctxt._1;
// //   let repr = locked_ctxt._2;
// //   let ctxt_lk = locked_ctxt._3;
// //   // TODO: would be nice to use a rename here, to transfer ownership to ctxt_lk
// //   L.acquire locked_ctxt._3;
// //   destroy_ctxt locked_ctxt._1;
// // }
// // ```



// (*
//   DestroyContext: Part of DPE API 
//   Destroy the context pointed to by the handle by freeing the
//   arrays in the context (zeroize the UDS, if applicable). Return
//   boolean indicating success. 
//   NOTE: Current implementation disregards session protocol 
// *)
// ```pulse
// fn destroy_context' (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
//   requires emp
//   returns b:bool
//   ensures emp
// {
//   rewrite emp as (session_state_perm InUse);
//   let st = take_session_state sid InUse;
//   match st
//   {
//     None ->
//     {
//       with s. rewrite (session_state_perm s) as emp;
//       false
//     }

//     Some st ->
//     {
//       with s. rewrite (session_state_perm s)
//                    as (session_state_perm st);
//       if not (Available? st)
//       {
//         rewrite (session_state_perm st) as emp;
//         rewrite emp as (session_state_perm SessionError);
//         let st' = take_session_state sid SessionError;
//         //TODO: Fix this by proving that st' must be present and InUse
//         drop_ (session_state_perm (dflt st' SessionError));
//         false
//       }
//       else if (ctxt_hndl = hndl_of st)
//       {
//         elim_session_state_perm_available st;
//         destroy_ctxt (ctxt_of st);
//         //reset the session to the start state
//         rewrite emp as (session_state_perm SessionStart);
//         let st' = take_session_state sid SessionStart;
//         //TODO: Fix this by proving that st' must be present and InUse
//         drop_ (session_state_perm (dflt st' SessionStart));
//         true
//       }
//       else
//       {
//         //context handle mismatch; put back st
//         //and return false
//         let st' = take_session_state sid st;
//         //TODO: Fix this by proving that st' must be present and InUse
//         drop_ (session_state_perm (dflt st' st));
//         false
//       }
//     }
//   }
// }
// ```

// let destroy_context = destroy_context'

// ```pulse
// fn ctxt_hndl_do_nothing (k:ctxt_hndl_t)
//   requires emp
//   ensures emp
// {
//   ()
// }
// ```


#push-options "--admit_smt_queries true"
```pulse
fn destroy_session_state (st:session_state)
  requires session_state_perm st
  ensures emp
{
  match st {
    Available st1 -> {
      elim_session_state_perm_available st;
      with e. rewrite (context_perm (ctxt_of st) e) as (context_perm st1.context e);
      destroy_ctxt st1.context;
    }
    _ -> {
      rewrite (session_state_perm st) as emp
    }
  }

  // if not (Available? st)
  // {
  //   rewrite (session_state_perm st) as emp
  // }
  // else 
  // {
  //   elim_session_state_perm_available st;
  //   destroy_ctxt (ctxt_of st);
  // }
}
```
#pop-options

// (* 
//   CloseSession: Part of DPE API 
//   Destroy the context table for the session and remove the reference
//   to it from the session table. Return boolean indicating success. 
//   NOTE: Current implementation disregards session protocol 
// *)
// ```pulse
// fn close_session' (sid:sid_t)
//   requires emp
//   returns b:bool
//   ensures emp
// {
//   rewrite emp as (session_state_perm InUse);
//   let st = take_session_state sid InUse;
//   match st 
//   {
//     None -> 
//     {
//       with s. rewrite (session_state_perm s) as emp;
//       false 
//     }

//     Some st ->
//     {
//       destroy_session_state st;
//       rewrite emp as (session_state_perm SessionClosed);
//       let st' = take_session_state sid SessionClosed;
//       //TODO: Fix this by proving that st' must be present and InUse
//       drop_ (session_state_perm (dflt st' SessionClosed));
//       true
//     }
//   }
// }
// ```
// let close_session = close_session'

// // TODO: 
// let prng () : U32.t = admit()


module V = Pulse.Lib.Vec

```pulse
fn init_engine_ctxt
  (uds:A.array U8.t { A.length uds == US.v uds_len })
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

  // V.to_array_pts_to uds;
  V.to_array_pts_to uds_buf;
  A.memcpy uds_len uds (V.vec_to_array uds_buf);
  // V.to_vec_pts_to uds;
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

```pulse
fn init_l0_ctxt
  (cdi:A.array U8.t { A.length cdi == US.v dice_digest_len })
  (#engine_repr:erased engine_record_repr)
  (#s:erased (Seq.seq U8.t))
  (#uds_bytes:erased (Seq.seq U8.t))
  (_:squash(cdi_functional_correctness s uds_bytes engine_repr /\
            l0_is_authentic engine_repr))
  requires A.pts_to cdi s
        ** pure (A.is_full_array cdi)
  returns ctxt:context_t
  ensures
    A.pts_to cdi s **
    (exists* repr.
     context_perm ctxt repr **
     pure (repr == L0_context_repr (mk_l0_context_repr_t uds_bytes s engine_repr)))
{
  let cdi_buf = V.alloc 0uy dice_digest_len;
  A.pts_to_len cdi;
  V.pts_to_len cdi_buf;

  // V.to_array_pts_to cdi;
  V.to_array_pts_to cdi_buf;
  A.memcpy dice_digest_len cdi (V.vec_to_array cdi_buf);
  // V.to_vec_pts_to cdi;
  V.to_vec_pts_to cdi_buf;
  
  // A.zeroize dice_digest_len cdi;
  // V.free cdi;

  let l0_context = mk_l0_context_t cdi_buf;
  let l0_context_repr = hide (mk_l0_context_repr_t uds_bytes s engine_repr);
  rewrite each cdi_buf as (l0_context.cdi);
  fold (l0_context_perm l0_context l0_context_repr);

  let ctxt = mk_context_t_l0 l0_context;
  let repr = mk_context_repr_t_l0 l0_context_repr;
  rewrite (l0_context_perm l0_context l0_context_repr) 
    as (context_perm ctxt repr);

  ctxt
}
```

```pulse
fn init_l1_ctxt (deviceIDCSR_len: US.t) (aliasKeyCRT_len: US.t) 
                (deviceID_priv: A.larray U8.t (US.v v32us)) (deviceID_pub: A.larray U8.t (US.v v32us))
                (aliasKey_priv: A.larray U8.t (US.v v32us)) (aliasKey_pub: A.larray U8.t (US.v v32us)) 
                (deviceIDCSR: A.larray U8.t (US.v deviceIDCSR_len)) (aliasKeyCRT: A.larray U8.t (US.v aliasKeyCRT_len))
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
  returns ctxt:context_t
  ensures 
    A.pts_to deviceID_priv deviceID_priv0 ** 
    A.pts_to deviceID_pub deviceID_pub0 **
    A.pts_to aliasKey_priv aliasKey_priv0 ** 
    A.pts_to aliasKey_pub aliasKey_pub0 ** 
    A.pts_to deviceIDCSR deviceIDCSR0 **
    A.pts_to aliasKeyCRT aliasKeyCRT0 **
    (exists* l1repr. 
      context_perm ctxt l1repr **
      pure (l1repr ==
            L1_context_repr (mk_l1_context_repr_t 
                              deviceID_label_len aliasKey_label_len deviceID_priv0 deviceID_pub0
                              aliasKey_priv0 aliasKey_pub0 aliasKeyCRT_len aliasKeyCRT0 deviceIDCSR_len
                              deviceIDCSR0 cdi repr deviceIDCSR_ingredients aliasKeyCRT_ingredients))
    )

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

  let ctxt = mk_context_t_l1 l1_context;
  let repr = mk_context_repr_t_l1 l1_context_repr;
  rewrite (l1_context_perm l1_context l1_context_repr) as (context_perm ctxt repr);
  ctxt  
}
```

assume val prng () : U32.t

(*
  InitializeContext: Part of DPE API 
  Create a context in the initial state (engine context) and store the context
  in the current session's context table. Return the context handle upon
  success and None upon failure. 
*)
```pulse
fn initialize_context
  (#p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  (sid:sid_t) (uds:A.larray U8.t (US.v uds_len)) 
                       
  requires A.pts_to uds #p uds_bytes
  returns _:option ctxt_hndl_t
  ensures A.pts_to uds #p uds_bytes
{
  rewrite emp as (session_state_perm InUse);
  let st = take_session_state sid InUse;
  match st
  {
    None ->
    {
      with s. rewrite (session_state_perm s) as emp;
      None #ctxt_hndl_t
    }
    
    Some st ->
    {
      match st {
        SessionStart -> {
          rewrite (session_state_perm st) as emp;
          let ctxt = init_engine_ctxt uds;
          let ctxt_hndl = prng ();
          let st' = intro_session_state_perm_available ctxt ctxt_hndl;
          let st'' = take_session_state sid st';
          //TODO: prove that st'' is InUse
          drop_ (session_state_perm (dflt st'' st'));
          Some ctxt_hndl
        }
        _ -> {
          destroy_session_state st;
          rewrite emp as (session_state_perm SessionError);
          let st' = take_session_state sid SessionError;
          //TODO: prove st' is InUse
          drop_ (session_state_perm (dflt st' SessionError));
          None #ctxt_hndl_t
        }
      }
      // if SessionStart? st 
      // {
      //   rewrite (session_state_perm st) as emp;
      //   let ctxt = init_engine_ctxt uds;
      //   let ctxt_hndl = prng ();
      //   let st' = intro_session_state_perm_available ctxt ctxt_hndl;
      //   let st'' = take_session_state sid st';
      //   //TODO: prove that st'' is InUse
      //   drop_ (session_state_perm (dflt st'' st'));
      //   Some ctxt_hndl
      // }
      // else //session error
      // {
      //   destroy_session_state st;
      //   rewrite emp as (session_state_perm SessionError);
      //   let st' = take_session_state sid SessionError;
      //   //TODO: prove st' is InUse
      //   drop_ (session_state_perm (dflt st' SessionError));
      //   None #ctxt_hndl_t
      // }
    }
  }
}
```

// let initialize_context = initialize_context'

(*
  RotateContextHandle: Part of DPE API 
  Invalidate the current context handle and replace it with a new context
  handle. Return the context handle upon success and None upon failure.
*)
```pulse
fn rotate_context_handle (sid:sid_t) (ctxt_hndl:ctxt_hndl_t)
  requires emp
  returns _:option ctxt_hndl_t
  ensures emp
{
  rewrite emp as (session_state_perm InUse);
  let st = take_session_state sid InUse;
  match st 
  {
    None ->
    {
      with s. rewrite (session_state_perm s) as emp;
      None #ctxt_hndl_t
    }

    Some st ->
    {
      match st {
        InUse -> {
          rewrite (session_state_perm st) as emp;
          None #ctxt_hndl_t
        }
        Available st1 -> {
          let new_ctxt_hndl = prng ();
          elim_session_state_perm_available st;
          with e. rewrite (context_perm (ctxt_of st) e) as (context_perm st1.context e);
          let st' = intro_session_state_perm_available st1.context new_ctxt_hndl;
          let st'' = take_session_state sid st';
          //TODO: prove st'' is InUse
          drop_ (session_state_perm (dflt st'' st'));
          Some new_ctxt_hndl
        }
        _ -> {
          //session error
          // assert (pure (~ (Available? st || InUse? st)));  // This is not provable?
          admit ()
          // rewrite (session_state_perm st) as emp;
          // rewrite emp as (session_state_perm SessionError);
          // let st' = take_session_state sid SessionError;
          // //TODO: prove st' is InUse
          // drop_ (session_state_perm (dflt st' SessionError));
          // None #ctxt_hndl_t
        }
      }
    //   if InUse? st
    //   { //block concurrent access
    //     rewrite (session_state_perm st) as emp;
    //     None #ctxt_hndl_t
    //   }
    //   else if not (Available? st)
    //   { //session error
    //     rewrite (session_state_perm st) as emp;
    //     rewrite emp as (session_state_perm SessionError);
    //     let st' = take_session_state sid SessionError;
    //     //TODO: prove st' is InUse
    //     drop_ (session_state_perm (dflt st' SessionError));
    //     None #ctxt_hndl_t
    //   }
    //   else 
    //   {
    //     let new_ctxt_hndl = prng ();
    //     elim_session_state_perm_available st;
    //     let st' = intro_session_state_perm_available (ctxt_of st) new_ctxt_hndl;
    //     let st'' = take_session_state sid st';
    //     //TODO: prove st'' is InUse
    //     drop_ (session_state_perm (dflt st'' st'));
    //     Some new_ctxt_hndl
    //   }      
    }
  }
}
```
// let rotate_context_handle = rotate_context_handle'

let maybe_context_perm (o:option context_t) =
  match o with
  | None -> emp
  | _ -> exists* repr. context_perm (Some?.v o) repr

// ```pulse
// fn intro_maybe_context_perm (c:context_t)
//   requires context_perm c 'repr
//   returns o:option context_t
//   ensures maybe_context_perm o
// {
//   rewrite (context_perm c 'repr)
//        as (context_perm (Some?.v (Some c)) 'repr);
//   fold (maybe_context_perm (Some c));
//   Some c
// }
// ```

```pulse
ghost
fn elim_maybe_context_perm (c:context_t)
  requires maybe_context_perm (Some c)
  ensures exists* repr. context_perm c repr
{
  unfold (maybe_context_perm (Some c));
  with x y. rewrite (context_perm x y) as (context_perm c y)
}
```

// ```pulse
// fn derive_child_from_context
//     (context:context_t)
//     (record:record_t)
//   requires
//     record_perm record p 'record_repr **
//     context_perm context 'context_repr
//   returns res:option context_t
//   ensures
//     record_perm record p 'record_repr **
//     context_perm context 'context_repr **
//     maybe_context_perm res
// {
//   match context
//   {
//     Engine_context c ->
//     {
//       if not (Engine_record? record)
//       { //illegal argument; reject
//         rewrite emp as (maybe_context_perm None);
//         None #context_t
//       }
//       else
//       {
//         rewrite each context as (Engine_context c);
//         let uds = get_engine_context_perm c 'context_repr;
//         // rewrite (context_perm (E) ctxt_repr) as (engine_context_perm c);
//         unfold (engine_context_perm c uds);
//         match record
//         {
//           Engine_record r ->
//           {
//             rewrite each record as (Engine_record r);
//             let r0 = get_engine_record_perm r 'record_repr p;
//             let cdi = A.alloc 0uy dice_digest_len;
//             let ret = EngineCore.engine_main cdi c.uds r;
//             with s. assert (A.pts_to cdi s);
//             fold (engine_context_perm c uds);
//             rewrite (engine_context_perm c uds)
//                  as (context_perm context 'context_repr);
//             match ret 
//             {
//               DICE_SUCCESS ->
//               {
//                 let l0_ctxt = init_l0_ctxt cdi #r0 #s #uds ();
//                 rewrite (engine_record_perm r p r0)
//                      as (record_perm record p 'record_repr);
//                 let l0_ctxt_opt = intro_maybe_context_perm l0_ctxt;
//                 l0_ctxt_opt
//               }

//               DICE_ERROR ->
//               {
//                 A.zeroize dice_digest_len cdi;
//                 A.free cdi;
//                 rewrite (engine_record_perm r p r0)
//                      as (record_perm record p 'record_repr);
//                 rewrite emp as (maybe_context_perm None);
//                 None #context_t
//               }
//             }
//           }
//         }
//       }
//     }
//     L0_context c ->
//     { 
//       if not (L0_record? record)
//       { //illegal argument; reject
//         rewrite emp as (maybe_context_perm None);
//         None #context_t
//       }
//       else
//       {
//         match record 
//         {
//           L0_record r ->
//           {
//             // NOTE: we won't eventually release l0_context_perm because we won't 
//             // own it anymore -- we will free the cdi array
//             rewrite each context as (L0_context c);
//             let cr = get_l0_context_perm c 'context_repr;
//             unfold (l0_context_perm c cr);
//             with s. assert (A.pts_to c.cdi s);

//             rewrite each record as (L0_record r);
//             let r0 = get_l0_record_perm r 'record_repr p;

//             let idcsr_ing = r.deviceIDCSR_ingredients;
//             let akcrt_ing = r.aliasKeyCRT_ingredients;

//             let deviceIDCRI_len = len_of_deviceIDCRI  idcsr_ing.version idcsr_ing.s_common 
//                                                       idcsr_ing.s_org idcsr_ing.s_country;
//             let aliasKeyTBS_len = len_of_aliasKeyTBS  akcrt_ing.serialNumber akcrt_ing.i_common 
//                                                       akcrt_ing.i_org akcrt_ing.i_country 
//                                                       akcrt_ing.s_common akcrt_ing.s_org 
//                                                       akcrt_ing.s_country akcrt_ing.l0_version;
//             let deviceIDCSR_len = length_of_deviceIDCSR deviceIDCRI_len;
//             let aliasKeyCRT_len = length_of_aliasKeyCRT aliasKeyTBS_len;

//             let mut deviceID_pub = [| 0uy; v32us |];
//             let mut deviceID_priv = [| 0uy; v32us |];
//             let mut aliasKey_pub = [| 0uy; v32us |];
//             let mut aliasKey_priv = [| 0uy; v32us |];
//             let mut deviceIDCSR = [| 0uy; deviceIDCSR_len |];
//             let mut aliasKeyCRT = [| 0uy; aliasKeyCRT_len |];
            
//             L0Core.l0_main  c.cdi deviceID_pub deviceID_priv 
//                             aliasKey_pub aliasKey_priv 
//                             aliasKeyTBS_len aliasKeyCRT_len aliasKeyCRT 
//                             deviceIDCRI_len deviceIDCSR_len deviceIDCSR r;
//             fold (l0_context_perm c cr);
//             rewrite (l0_context_perm c cr)
//                  as (context_perm context 'context_repr);
//             rewrite (l0_record_perm r p r0)
//                  as (record_perm record p 'record_repr);
//             let l1_context = init_l1_ctxt 
//                         deviceIDCSR_len aliasKeyCRT_len deviceID_priv deviceID_pub
//                         aliasKey_priv aliasKey_pub deviceIDCSR aliasKeyCRT
//                         (hide r.deviceID_label_len)
//                         (hide r.aliasKey_label_len) s r0 (hide idcsr_ing) (hide akcrt_ing);
//             intro_maybe_context_perm l1_context
//           }
//         }
//       }
//     }
//     L1_context _ ->
//     {
//       // ERROR - cannot invoke DeriveChild with L1 context
//       rewrite emp as (maybe_context_perm None);
//       None #context_t
//     }
//   }
// }
// ```


assume val derive_child_from_context (context:context_t) (record:record_t) p
  (#record_repr: erased repr_t) (#context_repr:erased (context_repr_t))
  : stt (context_t & option context_t)
        (requires record_perm record p record_repr **
                  context_perm context context_repr)
        (ensures fun res -> record_perm record p record_repr **
                            context_perm (fst res) context_repr **
                            maybe_context_perm (snd res))



(*
  DeriveChild: Part of DPE API 
  Execute the DICE layer associated with the current context and produce a 
  new context. Destroy the current context in the current session's context table 
  and store the new context in the table. Return the new context handle upon
  success and None upon failure. 
*)
```pulse
fn derive_child (sid:sid_t) (ctxt_hndl:ctxt_hndl_t) (record:record_t)
                (#repr:erased repr_t) (#p:perm)
  requires record_perm record p repr
  returns _:option ctxt_hndl_t
  ensures record_perm record p repr
{
  rewrite emp as (session_state_perm InUse);
  let st = take_session_state sid InUse;
  match st
  {
    None ->
    {
      with s. rewrite (session_state_perm s) as emp;
      None #ctxt_hndl_t
    }

    Some st ->
    {
      match st {
        InUse -> {
          //block concurrent access
          rewrite (session_state_perm st) as emp;
          None #ctxt_hndl_t
        }
        Available st1 -> {
          elim_session_state_perm_available st;
          with e. rewrite (context_perm (ctxt_of st) e) as (context_perm st1.context e);
          let next_ctxt = derive_child_from_context st1.context record p;
          destroy_ctxt (fst next_ctxt);
          match snd next_ctxt {
            None -> {
              rewrite emp as (session_state_perm SessionError);
              rewrite (maybe_context_perm (snd next_ctxt)) as emp;
              let st' = take_session_state sid SessionError;
              //TODO: prove st' is InUse
              drop_ (session_state_perm (dflt st' SessionError));
              None #ctxt_hndl_t
            }
            Some next_ctxt -> {
              elim_maybe_context_perm next_ctxt;
              let next_ctxt_hndl = prng();
              let st' = intro_session_state_perm_available next_ctxt next_ctxt_hndl;
              let st'' = take_session_state sid st';
              //TODO: prove st'' is InUse
              drop_ (session_state_perm (dflt st'' st'));
              Some next_ctxt_hndl
            }
          }
          // destroy_ctxt (ctxt_of st);
          // match next_ctxt {
          //   None -> {
          //     rewrite emp as (session_state_perm SessionError);
          //     rewrite (maybe_context_perm next_ctxt) as emp;
          //     let st' = take_session_state sid SessionError;
          //     //TODO: prove st' is InUse
          //     drop_ (session_state_perm (dflt st' SessionError));
          //     None #ctxt_hndl_t
          //   }
          //   Some next_ctxt -> {
          //     elim_maybe_context_perm next_ctxt;
          //     let next_ctxt_hndl = prng();
          //     let st' = intro_session_state_perm_available next_ctxt next_ctxt_hndl;
          //     let st'' = take_session_state sid st';
          //     //TODO: prove st'' is InUse
          //     drop_ (session_state_perm (dflt st'' st'));
          //     Some next_ctxt_hndl
          //   }
          // }
        }
        _ -> {
          admit ()
        }
      }
      // if InUse? st
      // { //block concurrent access
      //   rewrite (session_state_perm st) as emp;
      //   None #ctxt_hndl_t
      // }
      // else if not (Available? st)
      // { //session error
      //   rewrite (session_state_perm st) as emp;
      //   rewrite emp as (session_state_perm SessionError);
      //   let st' = take_session_state sid SessionError;
      //   //TODO: prove st' is InUse
      //   drop_ (session_state_perm (dflt st' SessionError));
      //   None #ctxt_hndl_t
      // }
      // else 
      // {
      //   elim_session_state_perm_available st;
      //   let next_ctxt = derive_child_from_context (ctxt_of st) record;
      //   destroy_ctxt (ctxt_of st);
      //   match next_ctxt
      //   {
      //     None ->
      //     {
      //       rewrite emp as (session_state_perm SessionError);
      //       rewrite (maybe_context_perm next_ctxt) as emp;
      //       let st' = take_session_state sid SessionError;
      //       //TODO: prove st' is InUse
      //       drop_ (session_state_perm (dflt st' SessionError));
      //       None #ctxt_hndl_t
      //     }

      //     Some next_ctxt ->
      //     {
      //       elim_maybe_context_perm next_ctxt;
      //       let next_ctxt_hndl = prng();
      //       let st' = intro_session_state_perm_available next_ctxt next_ctxt_hndl;
      //       let st'' = take_session_state sid st';
      //       //TODO: prove st'' is InUse
      //       drop_ (session_state_perm (dflt st'' st'));
      //       Some next_ctxt_hndl
      //     }
      //   }
      // }
    }
  }
}
```
// let derive_child = derive_child'
