module EngineCore
open EngineTypes
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module SZ = FStar.SizeT
open HACL

val l0_is_authentic (repr:engine_record_repr) : prop
val cdi_functional_correctness (c0:Seq.seq U8.t) (repr:engine_record_repr) : prop 

val engine_main (cdi:cdi_t) (uds:A.larray U8.t (SZ.v uds_len)) (record:engine_record_t)
                (#p:perm)
                (#c0:Ghost.erased (elseq U8.t dice_digest_len))
                (#repr:Ghost.erased engine_record_repr)
  : stt dice_return_code (A.pts_to uds p uds_bytes **
                          A.pts_to cdi full_perm c0 **
                          engine_record_perm record repr)
                         (fun r -> 
                            engine_record_perm record repr **
                            A.pts_to uds p uds_bytes **
                            exists_ (fun (c1:elseq U8.t dice_digest_len) ->
                                      A.pts_to cdi full_perm c1 **
                                      pure (A.is_full_array cdi
                                        /\ r = DICE_SUCCESS ==> l0_is_authentic repr /\ cdi_functional_correctness c1 repr)))