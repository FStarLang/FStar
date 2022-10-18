(*
   Copyright 2021 Microsoft Research

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

module Steel.C.Array
include Steel.C.Array.Base
open Steel.Memory
open Steel.FractionalPermission
open Steel.Effect
open FStar.Ghost
open Steel.Effect.Atomic

open Steel.C.Typedef
open Steel.C.Model.PCM
open Steel.C.Fields
open Steel.C.Typenat

#set-options "--ide_id_info_off"

/// Accesses index [i] in array [r], as long as [i] is in bounds and the array
/// is currently valid in memory

val index_from (#t:Type) (r:array_or_null_from t) (r' : array_or_null_to t { array_or_null_spec (r, r') /\ g_is_null (r, r') == false }) (i:size_t)
  : Steel t
             (varray (r, r'))
             (fun _ -> varray (r, r'))
             (requires fun _ -> size_v i < length (r, r'))
             (ensures fun h0 x h1 ->
               let s = h1 (varray (r, r')) in
               size_v i < length (r, r') /\
               h0 (varray (r, r')) == s /\
               x == Seq.index s (size_v i))

inline_for_extraction
let index (#t:Type) (r:array t) (i:size_t)
  : Steel t
             (varray r)
             (fun _ -> varray r)
             (requires fun _ -> size_v i < length r)
             (ensures fun h0 x h1 ->
               let s = h1 (varray r) in
               size_v i < length r /\
               h0 (varray r) == s /\
               x == Seq.index s (size_v i))
= match r with
  | (r0, r') ->
    change_equal_slprop
      (varray r)
      (varray (r0, r'));
    let res = index_from r0 r' i in
    change_equal_slprop
      (varray (r0, r'))
      (varray r);
    return res
  

/// Updates index [i] in array [r] with value [x], as long as [i]
/// is in bounds and the array is currently valid in memory


val upd_from (#t:Type) (r:array_or_null_from t) (r' : array_or_null_to t { array_or_null_spec (r, r') /\ g_is_null (r, r') == false }) (i:size_t) (x:t)
  : Steel unit
             (varray (r, r'))
             (fun _ -> varray (r, r'))
             (requires fun h -> size_v i < length (r, r'))
             (ensures fun h0 _ h1 ->
               size_v i < length (r, r') /\
               h1 (varray (r, r')) == Seq.upd (h0 (varray (r, r'))) (size_v i) x)

inline_for_extraction
let upd (#t:Type) (r:array t) (i:size_t) (x:t)
  : Steel unit
             (varray r)
             (fun _ -> varray r)
             (requires fun h -> size_v i < length r)
             (ensures fun h0 _ h1 ->
               size_v i < length r /\
               h1 (varray r) == Seq.upd (h0 (varray r)) (size_v i) x)
= match r with
  | (r0, r') ->
    change_equal_slprop
      (varray r)
      (varray (r0, r'));
    upd_from r0 r' i x;
    change_equal_slprop
      (varray (r0, r'))
      (varray r)
