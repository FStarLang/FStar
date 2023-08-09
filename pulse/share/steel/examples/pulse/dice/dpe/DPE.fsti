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
open Pulse.Lib.HashTable


// A record_t is passed from the caller to DeriveChild with any data necessary
// for DeriveChild to execute. 
// TODO: The input from the caller is given in wire format, so we need to 
// add a step parsing the input from, e.g. CBOR, into a record_t

val record_t : Type0

val repr_t : Type0 

val record_perm (t_rec:record_t) (t_rep:repr_t) : vprop

val ctxt_hndl_t : eqtype

val sid_t : eqtype

val open_session (_:unit) : stt (option sid_t) emp (fun _ -> emp)

val destroy_context (sid:sid_t) (ctxt_hndl:ctxt_hndl_t) : stt bool emp (fun _ -> emp)

val close_session (sid:sid_t) : stt bool emp (fun _ -> emp)

val initialize_context (sid:sid_t) (uds:A.larray U8.t (US.v uds_len)) (#p:perm)
  : stt (option ctxt_hndl_t) 
        (A.pts_to uds p uds_bytes ** 
         uds_is_enabled)
        (fun _ -> A.pts_to uds p uds_bytes)

val derive_child (sid:sid_t) (ctxt_hndl:ctxt_hndl_t) (record:record_t) (#repr:erased repr_t)
  : stt (option ctxt_hndl_t) 
        (record_perm record repr) 
        (fun _ -> record_perm record repr)