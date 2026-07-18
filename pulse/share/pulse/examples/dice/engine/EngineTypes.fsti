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

module EngineTypes
open Pulse.Lib.Pervasives
module V = Pulse.Lib.Vec
module US = FStar.SizeT
module U8 = FStar.UInt8
open HACL

val uds_len : hashable_len 

type dice_return_code = | DICE_SUCCESS | DICE_ERROR

let cdi_t = V.lvec U8.t (US.v (digest_len dice_hash_alg))

(* Engine Record *)
noeq
type engine_record_t = {
  l0_image_header_size : signable_len;
  l0_image_header      : V.lvec U8.t (US.v l0_image_header_size);
  l0_image_header_sig  : V.lvec U8.t 64; (* secret bytes *)
  l0_binary_size       : hashable_len;
  l0_binary            : V.lvec U8.t (US.v l0_binary_size);
  l0_binary_hash       : V.lvec U8.t (US.v dice_digest_len); (*secret bytes *)
  l0_image_auth_pubkey : V.lvec U8.t 32; (* secret bytes *)
}

type engine_record_repr = {
    l0_image_header      : Seq.seq U8.t;
    l0_image_header_sig  : Seq.seq U8.t;
    l0_binary            : Seq.seq U8.t;
    l0_binary_hash       : Seq.seq U8.t;
    l0_image_auth_pubkey : Seq.seq U8.t;
}

let mk_engine_repr  l0_image_header_size l0_image_header l0_image_header_sig
                    l0_binary_size l0_binary l0_binary_hash l0_image_auth_pubkey
  = {l0_image_header_size; l0_image_header; l0_image_header_sig;
     l0_binary_size; l0_binary; l0_binary_hash; l0_image_auth_pubkey}

let engine_record_perm (record:engine_record_t) (p:perm) (repr:engine_record_repr)
  : slprop = 
  pts_to record.l0_image_header #p repr.l0_image_header **
  pts_to record.l0_image_header_sig #p repr.l0_image_header_sig **
  pts_to record.l0_binary #p repr.l0_binary **
  pts_to record.l0_binary_hash #p repr.l0_binary_hash **
  pts_to record.l0_image_auth_pubkey #p repr.l0_image_auth_pubkey
