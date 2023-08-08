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


// hook this up to convert between wire format to pulse record
// demo engine and l0 rec type

(* Record *)
noeq
type record_t =
  | Engine_record : r:engine_record_t -> record_t
  | L0_record     : r:l0_record_t -> record_t

noeq
type repr_t = 
  | Engine_repr : r:engine_record_repr -> repr_t
  | L0_repr     : r:l0_record_repr -> repr_t

val record_perm (t_rec:record_t) (t_rep:repr_t) : vprop






// return a session id 
// use machine integers for sids and ctxt_hndl -- maybe make these abstract types
val open_session (_:unit) : stt bool emp (fun _ -> emp)

val destroy_context (sid:nat) (ctxt_hndl:nat) : stt bool emp (fun _ -> emp)

val close_session (sid:nat) : stt bool emp (fun _ -> emp)

// FIXME: dont need full perm on uds
val initialize_context (sid:nat) (uds:A.larray U8.t (US.v uds_len))
  : stt nat (A.pts_to uds full_perm uds_bytes ** 
             uds_is_enabled **
             pure (A.is_full_array uds))
            (fun _ -> A.pts_to uds full_perm uds_bytes)

val derive_child (sid:nat) (ctxt_hndl:nat) (record:record_t) (#repr:erased repr_t)
  : stt nat (record_perm record repr) 
            (fun _ -> record_perm record repr)