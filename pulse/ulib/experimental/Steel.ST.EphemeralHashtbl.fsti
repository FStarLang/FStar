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

type u32 = U32.t

/// Type of the hash functions

type hash_fn (k:eqtype) = k -> u32

/// Type of the vprops that related the key, value, and contents type

type vp_t (k:eqtype) (v contents:Type0) = k -> v -> contents -> vprop

/// The main hashtable table, indexed with a hash function and a vprop
val tbl
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (vp:vp_t k v contents)
  (h:hash_fn k)
  : Type0


/// The logical representation of the hashtable is a map from keys to contents,
///   thereby collapsing the value-indirection

type repr (k:eqtype) (contents:Type) = Map.t k contents


/// The hashtable separation logic permission
///
/// `tperm t m borrows` represents permission to a hashtable
///   whose concrete store is a partial view of `m`, and
///   all its entries that are present in `borrows` are currently borrowed

val tperm
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (t:tbl vp h)
  (m:repr k contents)
  (borrows:Map.t k v)
  : vprop

/// The create function
///
/// Returns the `tperm` with repr and borrows maps initialized to empty

inline_for_extraction
val create
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (vp:vp_t k v contents)
  (h:hash_fn k)
  (n:u32{U32.v n > 0})
  : STT (tbl vp h)
        emp
        (fun a -> tperm a (Map.empty k contents) (Map.empty k v))

/// A second create function that takes an erased contents value
///   and initializes the repr map to contain the erased value
///   for all the keys
///
/// Internally, the permission `tperm` relates seq entries to
///   the map, and does not specify any relation the other way round,
///   so it is possible to provide a const map initially

inline_for_extraction
val create_v
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (vp:vp_t k v contents)
  (h:hash_fn k)
  (n:u32{U32.v n > 0})
  (c:G.erased contents)
  : STT (tbl vp h)
        emp
        (fun a -> tperm a (Map.const k (G.reveal c)) (Map.empty k v))

/// Return type for `get`
///   - Present v: the key is present in the table, and is mapped to the value v
///   - Absent: the key is not in the table, and its "slot" does not contain any other key either
///   - Missing k': the key is not in the table, and its "slot" contains another key k'

type get_result (k:eqtype) (v:Type0) =
  | Present : v -> get_result k v
  | Absent
  | Missing : k -> get_result k v

unfold let map_contains_prop (#k:eqtype) (#v:Type0) (x:k) (m:Map.t k v) : prop =
  Map.contains m x == true

/// post vprop for `get`

let get_post 
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (m:G.erased (repr k contents))
  (borrows:G.erased (Map.t k v))
  (a:tbl vp h)
  (i:k)
  : get_result k v -> vprop
  = fun r ->
    match r, Map.sel m i with
    | Present x, Some c ->
      tperm a m (Map.upd borrows i x)  //when `get` succeeds, the key is added to `borrows`
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
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl vp h)
  (i:k)
  : ST (get_result k v)
       (tperm a m borrows)
       (get_post m borrows a i)
       (requires ~ (Map.contains borrows i))
       (ensures fun _ -> True)

/// `put` function
///
/// The key is removed from the borrows map,
///   and the representation map is updated accordingly

inline_for_extraction
val put
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl vp h)
  (i:k)
  (x:v)
  (c:G.erased contents)
  : STT unit
        (tperm a m borrows `star` vp i x c)
        (fun _ -> tperm a (Map.upd m i c) (Map.remove borrows i))


/// A ghost put function that returns the permission back to the table
///
/// The client also gets to update the represenation map

inline_for_extraction
val ghost_put (#opened:_)
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl vp h)
  (i:k)
  (x:v)
  (c:G.erased contents)
  : STGhost unit
            opened
            (tperm a m borrows `star` vp i x c)
            (fun _ -> tperm a (Map.upd m i c) (Map.remove borrows i))
            (requires Map.sel borrows i == Some x)
            (ensures fun _ -> True)

/// `remove` removes the key `i` from the concrete store, its mapping in the logical map is unchanged

inline_for_extraction
val remove
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#m:G.erased (Map.t k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl vp h)
  (i:k)
  : STT unit
        (tperm a m borrows)
        (fun _ -> tperm a m (Map.remove borrows i))


/// `free` frees the table and drops all the vp permissions

inline_for_extraction
val free
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Map.t k v))
  (a:tbl vp h)
  : STT unit
        (tperm a m borrows)
        (fun _ -> emp)
