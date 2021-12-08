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

   Authors: Aseem Rastogi
*)

module Steel.Hashtbl

open Steel.Memory
open Steel.ST.Effect.Ghost
open Steel.ST.Effect.Atomic
open Steel.ST.Effect
open Steel.ST.Util

module G = FStar.Ghost
module Map = FStar.PartialMap
module U32 = FStar.UInt32

type u32 = U32.t

type hash_fn (k:eqtype) = k -> u32

type vp_t (k:eqtype) (v contents:Type0) = k -> v -> contents -> vprop

type finalizer_t
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  = x:k -> y:v -> STT unit (exists_ (vp x y)) (fun _ -> emp)

val tbl
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (h:hash_fn k)
  (finalizer:finalizer_t vp)
  : Type0

type repr (k:eqtype) (contents:Type0) = Map.t k contents

val tperm
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (t:tbl h finalizer)
  (m:repr k contents)
  (borrows:Map.t k v)
  : vprop

inline_for_extraction
val create
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (h:hash_fn k)
  (finalizer:finalizer_t vp)
  (n:u32{U32.v n > 0})
  : STT (tbl h finalizer)
        emp
        (fun a -> tperm a (Map.empty k contents) (Map.empty k v))

type get_result (k:eqtype) (v:Type) =
  | Present : v -> get_result k v
  | Absent
  | Missing : k -> get_result k v

unfold let map_contains_prop (#k:eqtype) (#v:Type0) (x:k) (m:Map.t k v) : prop =
  Map.contains x m == true

let get_post 
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (m:G.erased (repr k contents))
  (borrows:G.erased (Map.t k v))
  (a:tbl h finalizer)
  (i:k)
  : get_result k v -> vprop
  = fun r ->
    match r, Map.sel i m with
    | Present x, Some c ->
      tperm a m (Map.upd i x borrows)
        `star`
      vp i x c
    | Present x, None -> pure False
    | Missing j, _ ->
      tperm a m borrows
        `star`
      pure (map_contains_prop j m)
    | _ -> tperm a m borrows

inline_for_extraction
val get
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl h finalizer)
  (i:k)
  : ST (get_result k v)
       (tperm a m borrows)
       (get_post m borrows a i)
       (requires ~ (Map.contains i borrows))
       (ensures fun _ -> True)

inline_for_extraction
val put
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl h finalizer)
  (i:k)
  (x:v)
  (c:G.erased contents)
  : STT unit
        (tperm a m borrows `star` vp i x c)
        (fun _ -> tperm a (Map.upd i (G.reveal c) m) (Map.remove i borrows))

let with_key_post
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (m:G.erased (repr k contents))
  (borrows:G.erased (Map.t k v))
  (a:tbl h finalizer)
  (i:k)
  (f_pre:vprop)
  (f_post:G.erased contents -> vprop)
  : get_result k (G.erased contents) -> vprop
  = fun r ->
    match r with
    | Present c ->
      tperm a (Map.upd i (G.reveal c) m) borrows
        `star`
      f_post c
    | Absent ->
      tperm a m borrows
        `star`
      f_pre
    | Missing j ->
      tperm a m borrows
        `star`
      f_pre
        `star`
      pure (map_contains_prop j m)

inline_for_extraction
val with_key
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl h finalizer)
  (i:k)
  (#f_pre:vprop) (#f_post:G.erased contents -> vprop)
  ($f:(i:k -> x:v -> c:G.erased contents -> STT (G.erased contents)
                                             (f_pre `star` vp i x c)
                                             (fun r -> f_post r `star` vp i x r)))
  : ST (get_result k (G.erased contents))
       (tperm a m borrows `star` f_pre)
       (with_key_post m borrows a i f_pre f_post)
       (requires ~ (Map.contains i borrows))
       (ensures fun _ -> True)

inline_for_extraction
val free
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (m:G.erased (repr k contents))
  (borrows:G.erased (Map.t k v))
  (a:tbl h finalizer)
  : STT unit
        (tperm a m borrows)
        (fun _ -> emp)
