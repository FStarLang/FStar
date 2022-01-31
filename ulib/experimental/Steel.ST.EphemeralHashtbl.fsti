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

module Steel.ST.EphemeralHashtbl

open Steel.Memory
open Steel.ST.Effect.Ghost
open Steel.ST.Effect.Atomic
open Steel.ST.Effect
open Steel.ST.Util

module G = FStar.Ghost
module Map = FStar.PartialMap
module U32 = FStar.UInt32

/// This module provides a basic hashtable with no support for hash-collisions
///
/// In particular, if the table already contains a key k1 and the client calls `put`
///   with another key k2 that has a hash-collision with k1, then k1 is evicted from the table
///
/// The table is designed to support reference-like types as values,
///   in addition to the usual `key` and `value` type, the table is also indexed with a `contents` type
///   and a separation logic proposition (`vprop`) that relates a key, value,
///   and the content that the value may point to
///
/// The content of the value is erased, the table does not store any concrete contents
///
/// During `put` the client provides this `vprop` relating the key, value, and
///   the (erased) contents, and on `get`, the client gets it back
///
/// To account for these permissions, the table also maintains a ghost
///   map that maintains keys that have been read (or borrowed)
///
/// The module provides a logical view of the hashtable as a map from keys to contents,
///   thereby collapsing the indirection of key -> value -> content
/// 
/// The logical map provides a hash-collision-free view of the table,
///   in the example above, the map would contain both k1 and k2, with the mapping for k1 unchanged by the `put` operation on k2 (unless k1 == k2)
///
/// So in that sense, the concrete state maintains a partial view of the logical map
///
/// The table may also be associated with a finalizer on values,
///   e.g. a free function if the values are references
///
/// The finalizer is invoked when the table is freed, or a key is evicted from the table,
///   unless the key is borrowed at the time, if so, client is responsible for finalizing

type u32 = U32.t

/// Type of the hash functions

type hash_fn (k:eqtype) = k -> u32

/// Type of the vprops that related the key, value, and contents type

type vp_t (k:eqtype) (v contents:Type0) = k -> v -> contents -> vprop

/// Type of a finalizer
///
/// It is a stateful function that consumes the vp permission

type finalizer_t
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  = x:k -> y:v -> STT unit (exists_ (vp x y)) (fun _ -> emp)

/// The main hashtable table, indexed with a hash function and the finalizer

val tbl
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (h:hash_fn k)
  (finalizer:finalizer_t vp)
  : Type0


/// The logical representation of the hashtable is a map from keys to contents,
///   thereby collapsing the value-indirection

type repr (k:eqtype) (contents:Type0) = Map.t k contents


/// The hashtable separation logic permission
///
/// `tperm t m borrows` represents permission to a hashtable
///   whose concrete store is a partial view of `m`, and
///   all its entries that are present in `borrows` are currently borrowed

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

/// The create function
///
/// Returns the `tperm` with repr and borrows maps initialized to empty

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

/// Return type for `get`
///   - Present v: the key is present in the table, and is mapped to the value v
///   - Absent: the key is not in the table, and its "slot" does not contain any other key either
///   - Missing k': the key is not in the table, and its "slot" contains another key k'

type get_result (k:eqtype) (v:Type) =
  | Present : v -> get_result k v
  | Absent
  | Missing : k -> get_result k v

unfold let map_contains_prop (#k:eqtype) (#v:Type0) (x:k) (m:Map.t k v) : prop =
  Map.contains x m == true

/// post vprop for `get`

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
      tperm a m (Map.upd i x borrows)  //when `get` succeeds, the key is added to `borrows`
        `star`
      vp i x c                         //in addition, we return the vp permission for the key

    | Present x, None -> pure False  //It can never be the case that the key is present in the table,
                                 //but is not mapped in the representation map
    | Missing j, _ ->
      tperm a m borrows
        `star`
      pure (map_contains_prop j m)

    | _ -> tperm a m borrows

/// `get` function

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

/// `put` function
///
/// The key is removed from the borrows map,
///   and the representation map is updated accordingly

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

/// with_key API
///
/// Suppose a client reads a key, works on the (key, value) pair returned,
///   and wishes to unborrow the key, not updating the value (may be updating the contents)
///
/// The only way to do it so far is for the client to call `get` and then `put`
///
/// However, `put` incurs a stateful write, which is unnecessary for such cases
///
/// Using `with_key`, the client may avoid this extra write,
///   by passing-in the computation they intend to do on the (key, value) pair

let with_key_post_present_predicate
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (m:G.erased (repr k contents))
  (borrows:G.erased (Map.t k v))
  (a:tbl h finalizer)
  (i:k)
  (#res:Type)
  (f_post:contents -> contents -> res -> vprop)
  (c:contents)
  (r:res)
  : contents -> vprop
  = fun c' -> 
    tperm a (Map.upd i (G.reveal c') m) borrows
      `star`
    f_post c (G.reveal c') r

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
  (#res:Type)
  (f_pre:vprop)
  (f_post:contents -> contents -> res -> vprop)
  : get_result k res -> vprop
  = fun r ->
    match r, Map.sel i m with
    | Present r, Some c ->
      exists_ (with_key_post_present_predicate m borrows a i f_post c r)
    | Present _, None -> pure False
    | Absent, _ ->
      tperm a m borrows
        `star`
      f_pre
    | Missing j, _ ->
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
  (#res:Type)
  (#f_pre:vprop) (#f_post:contents -> contents -> res -> vprop)
  ($f:(x:v -> c:G.erased contents -> STT res
                                       (f_pre `star` vp i x c)
                                       (fun r -> exists_ (fun c' -> f_post c c' r `star` vp i x c'))))
  : ST (get_result k res)
       (tperm a m borrows `star` f_pre)
       (with_key_post m borrows a i f_pre f_post)
       (requires ~ (Map.contains i borrows))
       (ensures fun _ -> True)


/// `remove` removes the key `i` from the concrete store, its mapping in the logical map is unchanged
///
/// The return value is `true` if `i` was present in the concrete store
///   `false` if `i` was not present in the concrete store when the client called `remove`
///
/// In case `i` was present, it also calls the finalizer on the `i` value

inline_for_extraction
val remove
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#m:G.erased (Map.t k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl h finalizer)
  (i:k)
  : STT bool
        (tperm a m borrows)
        (fun _ -> tperm a m borrows)


/// `free`, calls finalizer on all the values in the table,
///   unless the corresponding key is borrowed

inline_for_extraction
val free
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl h finalizer)
  : STT unit
        (tperm a m borrows)
        (fun _ -> emp)
