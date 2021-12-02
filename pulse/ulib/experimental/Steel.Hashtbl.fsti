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
module Set = FStar.Set
module Map = FStar.Map
module U32 = FStar.UInt32

/// This module provides a basic hashtable with no support for hash-collisions
///
/// In particular, if the table already contains a key k1 and the client invokes `put` API
///   with another key k2 that has a hash-collision with k1, then k1 is removed from the table
///
/// The module also provides a logical view of the hashtable as a map
///
/// The logical map provides a hash-collision-free view of the table,
///   in the example above, the map would contain both k1 and k2, with the mapping for k1 unchanged by the `put` operation on k2 (unless k1 == k2)
///
/// So in that sense, the concrete state maintains a partial view of the map

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

let empty_repr (#k:eqtype) (#contents:Type0) (x:contents)
  : G.erased (repr k contents)
  = Map.restrict Set.empty (Map.const x)

val tperm
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (t:tbl h finalizer)
  (m:repr k contents)
  (borrows:Set.set k)
  : vprop

inline_for_extraction
val create
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (h:hash_fn k)
  (finalizer:finalizer_t vp)
  (n:u32{U32.v n > 0})
  (x:G.erased contents)
  : STT (tbl h finalizer)
      emp
      (fun a -> tperm a (empty_repr (G.reveal x)) Set.empty)

inline_for_extraction
val get
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Set.set k))
  (a:tbl h finalizer)
  (i:k)
  : ST (option v)
       (tperm a m borrows)
       (fun r ->
        match r with
        | None -> tperm a m borrows
        | Some x -> tperm a m (Set.add i borrows) `star` vp i x (Map.sel m i))
       (requires not (Set.mem i borrows))
       (ensures fun r -> Some? r ==> Map.contains m i)

inline_for_extraction
val put
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Set.set k))
  (a:tbl h finalizer)
  (i:k)
  (x:v)
  (c:G.erased contents)
  : STT unit
        (tperm a m borrows `star` vp i x c)
        (fun _ -> tperm a (Map.upd m i c) (Set.remove i borrows))

val ghost_put (#opened:_)
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#m:G.erased (repr k contents))
  (#borrows:G.erased (Set.set k))
  (a:tbl h finalizer)
  (i:k)
  (x:v)
  (c:G.erased contents)
  : STGhost unit opened
            (tperm a m borrows `star` vp i x (G.reveal c))
            (fun _ -> tperm a m (Set.remove i borrows))
            (requires Set.mem i borrows /\ Map.sel m i == G.reveal c)
            (ensures fun _ -> True)

inline_for_extraction
val free (#k:eqtype) (#v:Type0) (#h:hash_fn k) (#m:G.erased (repr k v)) (a:tbl k v h)
  : SteelT unit
      (tpts_to a m)
      (fun _ -> emp)
