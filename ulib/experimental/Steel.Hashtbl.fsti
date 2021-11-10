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
open Steel.Effect
open Steel.Effect.Atomic

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

/// A hash function is a total function that maps keys of type k to u32

type hash_fn (k:eqtype) = k -> u32

/// The hashtable type indexed by the key type, the value type, and the hash function

val tbl (k:eqtype) (v:Type0) (h:hash_fn k) : Type0

/// Logical view of the hash table is a map

type repr (k:eqtype) (v:Type0) = Map.t k v

let empty_repr (#k:eqtype) (#v:Type0) (x:v) : G.erased (repr k v) =
  Map.restrict Set.empty (Map.const x)

/// The main separation logic assertion for the hashtable,
///   saying that in the current heap, the tbl is a partial view of the map m

val tpts_to (#k:eqtype) (#v:Type0) (#h:hash_fn k) (t:tbl k v h) (m:repr k v) : vprop


/// create API
///
/// Takes an erased witness for the value type,
///   returns an empty hashtable
///
/// n is a hint to the implementation for its internal memory allocation
///   (roughly the number of keys that the client expects to be active at a given time)

inline_for_extraction
val create (#k:eqtype) (#v:Type0) (h:hash_fn k) (x:G.erased v) (n:u32{U32.v n > 0})
  : SteelT (tbl k v h)
      emp
      (fun a -> tpts_to a (empty_repr (G.reveal x)))

/// get API
///
/// It is a partial function,
///   if it succeeds then the returned value is related to the logical map view of the table

inline_for_extraction
val get (#k:eqtype) (#v:Type0) (#h:hash_fn k) (#m:G.erased (repr k v)) (a:tbl k v h) (i:k)
  : Steel (option v)
      (tpts_to a m)
      (fun _ -> tpts_to a m)
      (fun _ -> True)
      (fun _ r _ -> Some? r ==> r == Some (Map.sel m i))

/// put API

inline_for_extraction
val put (#k:eqtype) (#v:Type0) (#h:hash_fn k) (#m:G.erased (repr k v)) (a:tbl k v h) (i:k) (x:v)
  : SteelT unit
      (tpts_to a m)
      (fun _ -> tpts_to a (Map.upd m i x))


/// free API

inline_for_extraction
val free (#k:eqtype) (#v:Type0) (#h:hash_fn k) (#m:G.erased (repr k v)) (a:tbl k v h)
  : SteelT unit
      (tpts_to a m)
      (fun _ -> emp)
