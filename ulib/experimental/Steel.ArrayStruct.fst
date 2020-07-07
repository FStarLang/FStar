(*
   Copyright 2020 Microsoft Research

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

module Steel.ArrayStruct

module SizeT = Steel.SizeT
module Map = FStar.Map


open FStar.FunctionalExtensionality
open Steel.PCM
module PCMBase = Steel.PCM.Base

open Steel.Effect
open Steel.Memory

let extract_update: unit -> Tot unit = (fun () -> ())
let extract_get: unit -> Tot unit = (fun () -> ())
let extract_explode: unit -> Tot unit = (fun () -> ())
let extract_recombine: unit -> Tot unit = (fun () -> ())
let op_String_Access : unit -> Tot unit = (fun () -> ())
let generic_index: unit -> Tot unit = (fun () -> ())

#set-options "--fuel 0 --ifuel 1"

let update_x
  (r: ref (option u32_pair) u32_pair_pcm)
  (old_pair: Ghost.erased u32_pair)
  (new_val: UInt32.t)
    : SteelT unit
      (pts_to r (Some (Ghost.reveal old_pair)))
      (fun _ -> pts_to r (Some ({ old_pair with x = new_val})))
  =
  let real_old_pair =  read r (Some (Ghost.reveal old_pair)) in
  let new_pair = (Some ({Some?.v real_old_pair with x = new_val })) in
  write r (Some (Ghost.reveal old_pair)) new_pair

let get_x
  (r: ref (option u32_pair) u32_pair_pcm)
  (pair: Ghost.erased u32_pair)
    : SteelT (x:UInt32.t{pair.x == x})
      (pts_to r (Some (Ghost.reveal pair)))
      (fun x -> (pts_to r (Some (Ghost.reveal pair))))
  =
  let real_pair = read r (Some (Ghost.reveal pair)) in
  (Some?.v real_pair).x

let increment_generic
  (#cls: rw_pointer UInt32.t)
  (r: cls.pointer_ref)
  (v: Ghost.erased UInt32.t{UInt32.v v + 1 <= UInt.max_int 32})
    : SteelT unit
      (cls.pointer_slref r v)
      (fun _ -> cls.pointer_slref r (UInt32.add v 1ul))
  =
  let old_v = cls.pointer_get r v in
  cls.pointer_upd r v (UInt32.add old_v 1ul)

let u32_pair_get : rw_pointer_get_sig u32_pair u32_pair_ref slu32_pair =
  fun r g_pair ->
    let Some (Full pair) = read r (Some (Full (Ghost.reveal g_pair))) in
    pair

let u32_pair_upd: rw_pointer_upd_sig u32_pair u32_pair_ref slu32_pair =
  fun r g_pair v ->
    let Some (Full pair) = read r (Some (Full (Ghost.reveal g_pair))) in
    write r (Some (Full (Ghost.reveal g_pair))) (Some (Full v))

let u32_pair_x_field_get
  : rw_pointer_get_sig UInt32.t u32_pair_x_field_ref slu32_pair_x_field
  =
  fun r g_x ->
    match read r (Some (XField g_x)) with
    | Some (XField x) -> x
    | Some (Full pair) -> pair.x

#push-options "--admit_smt_queries true"
let u32_pair_x_field_upd
  : rw_pointer_upd_sig UInt32.t u32_pair_x_field_ref slu32_pair_x_field
  =
  fun r g_x v ->
   let new_val = match read r (Some (XField g_x)) with
   | Some (XField x) -> Some (XField v)
   | Some (Full pair) -> Some (Full ({pair with x = v}))
   in
   assert(FStar.PCM.frame_preserving u32_pair_stored_pcm (Some (XField g_x)) new_val);
   write r (Some (XField g_x)) new_val
#pop-options

let u32_pair_y_field_get
  : rw_pointer_get_sig UInt32.t u32_pair_y_field_ref slu32_pair_y_field
  =
  admit()

let u32_pair_y_field_upd
  : rw_pointer_upd_sig UInt32.t u32_pair_y_field_ref slu32_pair_y_field
  =
  admit()

let recombinable (r: u32_pair_ref) (r12: u32_pair_x_field_ref & u32_pair_y_field_ref) : prop
  = admit()

let explose_u32_pair_into_x_y (r: u32_pair_ref) (pair: u32_pair)
  : SteelT (r12:(u32_pair_x_field_ref & u32_pair_y_field_ref){recombinable r r12})
  (slu32_pair r pair)
  (fun (r1, r2) ->
    slu32_pair_x_field r1 pair.x `star`
    slu32_pair_y_field r2 pair.y)
  =
  Steel.SteelT.Basics.h_admit _ _

let recombine_u32_pair_from_x_y
  (r: u32_pair_ref)
  (r1: u32_pair_x_field_ref)
  (v1: UInt32.t)
  (r2: u32_pair_y_field_ref)
  (v2: UInt32.t)
  : SteelT unit
    (slu32_pair_x_field r1 v1 `star` slu32_pair_y_field r2 v2)
    (fun _ -> slu32_pair r ({ x = v1; y = v2}))
  =
  Steel.SteelT.Basics.h_admit _ _
