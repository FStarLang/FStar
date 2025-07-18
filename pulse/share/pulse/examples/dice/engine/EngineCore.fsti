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

module EngineCore
open EngineTypes
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module US = FStar.SizeT
open HACL
#lang-pulse

noextract
val l0_is_authentic (repr:engine_record_repr) : prop

noextract
val cdi_functional_correctness (c0:Seq.seq U8.t) (uds_bytes:Seq.seq U8.t) (repr:engine_record_repr) : prop 

fn engine_main
  (cdi:A.larray U8.t (SZ.v (digest_len dice_hash_alg)))
  (uds:A.larray U8.t (US.v uds_len)) (record:engine_record_t)
  (#c0:Ghost.erased (Seq.seq U8.t))
  (#repr:Ghost.erased engine_record_repr)
  (#uds_perm #p:perm) (#uds_bytes:Ghost.erased (Seq.seq U8.t))
  requires engine_record_perm record p repr **
           pts_to uds #uds_perm uds_bytes **
           pts_to cdi c0
  returns  r:(engine_record_t & dice_return_code)
  ensures  engine_record_perm (fst r) p repr **
           pts_to uds #uds_perm uds_bytes **
          (exists* (c1:Seq.seq U8.t).
             pts_to cdi c1 **
             pure (snd r = DICE_SUCCESS ==> l0_is_authentic repr /\ cdi_functional_correctness c1 uds_bytes repr))