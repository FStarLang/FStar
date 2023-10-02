module EngineTypes
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
open HACL

let uds_is_enabled : vprop 
= admit()

let uds_len : hashable_len 
= admit()

let uds_bytes : Ghost.erased (elseq U8.t uds_len) 
= admit()
