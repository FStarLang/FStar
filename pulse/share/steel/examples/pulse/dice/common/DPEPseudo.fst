module DPEPseudo
open Pulse.Main
open Pulse.Steel.Wrapper
open FStar.Ghost
open Steel.ST.Util 
open Steel.ST.Array
open Steel.FractionalPermission
module A = Steel.ST.Array
module R = Steel.ST.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32


noeq
type context_t = 
  | Engine_context  : uds:A.array U8.t -> 
                      context_t
  | L0_context      : cdi:A.larray U8.t 32 -> 
                      context_t
  | L1_context      : aliasKey_priv:A.larray U8.t 32 ->
                      cert_aliasKey:A.array U8.t ->
                      csr_deviceID:A.array U8.t ->
                      context_t

(*

// init_dpe: Internal to DPE 
// Create the session table and session table lock. 
fn init_dpe ()
{
  let session_tbl = (new_table);

  (* the following should be GLOBAL state *)
  let session_tbl_lock = new_lock (exists s. A.pts_to session_tbl full_perm s); 
  let session_id_ctr = R.ref US.t;
  session_id_ctr := 0;
}


// OpenSession: Part of DPE API 
// Create a context table and context table lock for the new session. 
// Add the context table lock to the session table. 
fn OpenSession ()
{
  let ctxt_tbl = (new_table);
  let ctxt_tbl_lock = new_lock (exists s. A.pts_to ctxt_tbl full_perm s);
  
  let cur_session = !session_id_ctr;
  let session_tbl = acquire session_tbl_lock;
  store session_tbl cur_session ctxt_tbl_lock;

  session_id_ctr := cur_session + 1;
}


// CloseSession: Part of DPE API 
// Create a context table and context table lock for the new session. 
// Add the context table lock to the session table. 
fn CloseSession ()
{
  let ctxt_tbl = (new_table);
  let ctxt_tbl_lock = new_lock (exists s. A.pts_to ctxt_tbl full_perm s);
  
  let cur_session = !session_id_ctr;
  let session_tbl = acquire session_tbl_lock;
  store session_tbl cur_session ctxt_tbl_lock;
}


// InitializeContext: Part of DPE API 
// Create a context in the initial state (engine context) and store the context
// in the current session's context table. 
fn InitializeContext (seed:A.array U8.t) : A.array U32.t
{
  let ctxt = Engine_context seed;
  let ctxt_hndl = (PRNG);

  let cur_session = !session_id_ctr;
  let session_tbl = acquire session_tbl_lock;
  let ctxt_tbl_lock = get session_tbl cur_session;
  let ctxt_tbl = acquire ctxt_tbl_lock;
  
  store ctxt_tbl ctxt_hndl ctxt;
  ctxt_hndl
}


// DeriveChild: Part of DPE API 
// Execute the DICE layer associated with the current context and produce a 
// new context. Destroy the current context in the current session's context table 
// and store the new context in the table. 
fn DeriveChild (ctxt_hndl:A.array U32.t) (data:A.array U32.t) : A.array U32.t
{
  let cur_session = !session_id_ctr;
  let session_tbl = acquire session_tbl_lock;
  let ctxt_tbl_lock = get session_tbl cur_session;
  let ctxt_tbl = acquire ctxt_tbl_lock;

  let ctxt = get ctxt_tbl ctxt_hndl;
  let new_hndl = (PRNG);
  let new_ctxt: context_t = match ctxt
  | Engine_context -> (
      let engine_record = init_engine ctxt.uds data;
      let cdi = engine_main engine_record;
      L0_context cdi
    )
  | L0_context -> (
      let l0_record = init_l0 ctxt.cdi data;
      let (aliasKey_priv, cert_aliasKey, csr_deviceID) = l0_main l0_record;
      L1_context aliasKey_priv cert_aliasKey csr_deviceID
    )
  | _ -> Error;

  destroy ctxt_tbl ctxt_hndl;
  store ctxt_tbl new_hndl new_ctxt;
  new_hndl
}


// init_engine: Internal to DPE
// Build the record of DICE Engine state given the uds and l0 image
fn init_engine (uds:A.array U8.t) (l0_image:A.array U32.t) : engine_record_t
{
  ...
}


// init_l0: Internal to DPE
// Build the record of DICE L0 state given the cdi and fwid
fn init_l0 (cdi:A.larray U8.t 32) (fwid:A.array U32.t) : l0_record_t
{
  ...
}

*)