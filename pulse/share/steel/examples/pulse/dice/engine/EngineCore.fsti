module EngineCore
open EngineTypes
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module SZ = FStar.SizeT
open HACL

val l0_is_authentic (repr:engine_record_repr) : prop
val cdi_functional_correctness (c0:Seq.seq U8.t) (uds_bytes:Seq.seq U8.t) (repr:engine_record_repr) : prop 

val engine_main (cdi:cdi_t) (uds:A.larray U8.t (SZ.v uds_len)) (record:engine_record_t)
                (#c0:Ghost.erased (Seq.seq U8.t))
                (#repr:Ghost.erased engine_record_repr)
                (#uds_perm #p:perm)
                (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  : stt dice_return_code (engine_record_perm record p repr **
                          A.pts_to uds #uds_perm uds_bytes **
                          A.pts_to cdi c0)
                         (fun r -> 
                            engine_record_perm record p repr **
                            A.pts_to uds #uds_perm uds_bytes **
                            (exists* (c1:Seq.seq U8.t).
                                      A.pts_to cdi c1 **
                                      pure (r = DICE_SUCCESS ==>
                                            l0_is_authentic repr /\ cdi_functional_correctness c1 uds_bytes repr)))