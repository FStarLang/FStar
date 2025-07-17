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

module Pulse.Lib.Array.Core
#lang-pulse
open Pulse.Main
open Pulse.Lib.Core
module H = Pulse.Lib.HigherArray
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq

let base_t = H.base_t
inline_for_extraction
let array a = H.array a
let length #a x = H.length x
let base_of x = H.base_of x
let offset_of x = H.offset_of x
let is_full_array #a x = H.is_full_array x

inline_for_extraction
let null #a : array a = H.null
inline_for_extraction
let is_null r = H.is_null r

[@@pulse_unfold]
let pts_to_mask #t ([@@@mkey] a: array t) (#[full_default()] f: perm) (v: erased (Seq.seq t)) (mask: nat -> prop) : slprop =
  H.pts_to_mask a #f v mask

let pts_to_mask_timeless (#a:Type) (x:array a) (p:perm) (s:Seq.seq a) mask =
  ()

let pts_to_mask_len a = H.pts_to_mask_len a
let pts_to_mask_not_null r = H.pts_to_mask_not_null r

let mask_vext arr = H.mask_vext arr
let mask_mext arr = H.mask_mext arr
let mask_ext arr = H.mask_ext arr

let mask_share arr = H.mask_share arr
let mask_gather arr = H.mask_gather arr

let split_mask arr = H.split_mask arr
let join_mask arr = H.join_mask arr
let join_mask' arr = H.join_mask' arr

let pts_to_mask_injective_eq arr = H.pts_to_mask_injective_eq arr

inline_for_extraction let mask_read a = H.mask_read a
inline_for_extraction let mask_write a = H.mask_write a

let gsub arr = H.gsub arr

let gsub_intro arr = H.gsub_intro arr
let gsub_elim arr = H.gsub_elim arr

inline_for_extraction let sub arr = H.sub arr
let return_sub arr = H.return_sub arr

let pts_to r = H.pts_to r

let to_mask arr = H.to_mask arr
let from_mask arr = H.from_mask arr

let pts_to_timeless _ _ _ = ()
let pts_to_len a = H.pts_to_len a

inline_for_extraction let alloc x = H.alloc x

inline_for_extraction let op_Array_Access a = H.op_Array_Access a
inline_for_extraction let op_Array_Assignment a = H.op_Array_Assignment a

inline_for_extraction let free a = H.free a

let share arr = H.share arr
let gather arr = H.gather arr

let pts_to_range x = H.pts_to_range x

let pts_to_range_timeless _ _ _ _ _ = ()

let pts_to_range_prop a = H.pts_to_range_prop a

let pts_to_range_intro a = H.pts_to_range_intro a
let pts_to_range_elim a = H.pts_to_range_elim a

let pts_to_range_split a = H.pts_to_range_split a
let pts_to_range_join a = H.pts_to_range_join a

inline_for_extraction let pts_to_range_index a = H.pts_to_range_index a
inline_for_extraction let pts_to_range_upd a = H.pts_to_range_upd a

let pts_to_range_share arr = H.pts_to_range_share arr
let pts_to_range_gather arr = H.pts_to_range_gather arr

let with_pre (pre:slprop) (#a:Type) (#post:a -> slprop)(m:stt a emp post)
: stt a pre (fun v -> pre ** post v)
= let m1 = frame_stt pre m in
  let pf_post : slprop_post_equiv (fun r -> post r ** pre) (fun r -> pre ** post r)
    = intro_slprop_post_equiv _ _ (fun r -> slprop_equiv_comm (post r) pre)
  in
  sub_stt _ _ (slprop_equiv_unit pre) pf_post m1


fn alloc_with_pre
    (#a:Type u#0)
    (init:a)
    (len:SZ.t)
    (pre:slprop)
  requires pre
  returns arr:array a
  ensures (pre **
         (pts_to arr (Seq.create (SZ.v len) init) ** (
          pure (is_full_array arr) **
          pure (length arr == SZ.v len)))) **
        pure (is_full_array arr)
{
  alloc init len
}



fn free_with_post (#a:Type u#0) (arr:array a) (post:slprop)
  requires (post ** (exists* v. pts_to arr v)) ** pure (is_full_array arr)
  ensures post
{
  free arr  
}

(* this is universe-polymorphic in ret_t; so can't define it in Pulse yet *)
let with_local
    (#a:Type u#0)
    (init:a)
    (len:SZ.t)
    (#pre:slprop)
    (ret_t:Type u#a)
    (#post:ret_t -> slprop) 
      (body:(arr:array a) -> stt ret_t (pre **
                                    (pts_to arr (Seq.create (SZ.v len) init) ** (
                                     pure (is_full_array arr) **
                                     pure (length arr == SZ.v len))))
                                   (fun r -> post r ** (exists* v. pts_to arr v)))

: stt ret_t pre post
= let m1 = alloc_with_pre init len pre in
   let body (arr:array a)
    : stt ret_t 
         ((pre ** 
          (pts_to arr (Seq.create (SZ.v len) init) ** (
           pure (is_full_array arr) **
           pure (length arr == SZ.v len)))) **
         pure (is_full_array arr))
        post
    = bind_stt
        (frame_stt (pure (is_full_array arr)) (body arr))
        (fun r ->
          bind_stt
            (free_with_post arr (post r)) 
            (fun _ -> return_stt_noeq r post))
  in
  bind_stt m1 body
