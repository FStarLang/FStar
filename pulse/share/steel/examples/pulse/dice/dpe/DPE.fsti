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
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
open Pulse.Lib.HashTable

val ctxt_hndl_t : eqtype

val sid_t : eqtype

val get_profile (_:unit) : stt profile_descriptor_t emp (fun _ -> emp)

val open_session (_:unit) : stt (option sid_t) emp (fun _ -> emp)

val destroy_context (sid:sid_t) (ctxt_hndl:ctxt_hndl_t) : stt bool emp (fun _ -> emp)

val close_session (sid:sid_t) : stt bool emp (fun _ -> emp)

val initialize_context (sid:sid_t) (uds:A.larray U8.t (US.v uds_len)) (#p:perm)
  : stt (option ctxt_hndl_t) 
        (A.pts_to uds p uds_bytes ** 
         uds_is_enabled)
        (fun _ -> A.pts_to uds p uds_bytes)

val rotate_context_handle (sid:sid_t) (ctxt_hndl:ctxt_hndl_t) : stt (option ctxt_hndl_t) emp (fun _ -> emp)

val derive_child (sid:sid_t) (ctxt_hndl:ctxt_hndl_t) (record:record_t) (#repr:erased repr_t)
  : stt (option ctxt_hndl_t) 
        (record_perm record repr) 
        (fun _ -> record_perm record repr)