module DPE.CBOR
open Pulse.Lib.Pervasives
open DPESafe
open DPE
open EngineTypes
open DPETypes
open EngineCore
open DPEStateful
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module A = Pulse.Lib.Array

(* placeholder *)
val parse_cbor (b:bytes) (#a:Type0) (x:a) : prop

val initialize_context (len:SZ.t)
                       (input:A.larray U8.t (SZ.v len))
                       (len':SZ.t)
                       (output:A.larray U8.t (SZ.v len'))
                       (#input_bytes:Ghost.erased bytes)
  : stt bool
    (requires
      A.pts_to input input_bytes **
      exists_ (fun s -> A.pts_to output s))
    (ensures fun b ->
      A.pts_to input input_bytes **
      exists_ (fun output_bytes -> 
        A.pts_to output output_bytes **
        (if not b
         then emp
         else (
            exists_ (fun (sid:sid_t) ->
            exists_ (fun (uds:bytes) ->
            exists_ (fun (hndl:ctxt_hndl_t) ->
                pure (parse_cbor input_bytes (sid, uds) /\
                      parse_cbor output_bytes hndl) **
                snapshot sid (EngineInitialized hndl uds)
            )))
        ))))
        