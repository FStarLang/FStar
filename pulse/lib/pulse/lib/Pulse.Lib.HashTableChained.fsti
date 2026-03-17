(*
   Copyright 2024 Microsoft Research

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

(**
  A hash table implementation with separate chaining.
  
  The hash table is represented as a vector of buckets, where each bucket
  is a linked list of key-value pairs. The hash function maps keys to SZ.t
  which is then reduced modulo capacity to get the bucket index.
*)

module Pulse.Lib.HashTableChained

#lang-pulse

open Pulse.Lib.Pervasives
open FStar.Ghost
module SZ = FStar.SizeT
module FE = FStar.FunctionalExtensionality
module FS = FStar.FiniteSet.Base

(** Pure specification: hash table as a partial map using extensional functions *)
let pmap (k:eqtype) (v:Type0) = FE.restricted_t k (fun _ -> option v)

let empty_pmap #k #v : pmap k v = FE.on_dom k (fun _ -> None)

let lookup_pmap #k #v (m:pmap k v) (key:k) : option v = m key

let insert_pmap #k #v (m:pmap k v) (key:k) (value:v) : pmap k v =
  FE.on_dom k (fun k' -> if k' = key then Some value else m k')

let remove_pmap #k #v (m:pmap k v) (key:k) : pmap k v =
  FE.on_dom k (fun k' -> if k' = key then None else m k')

(** Key set derived from pmap *)
let keys_of_pmap (#k:eqtype) (#v:Type0) (m:pmap k v) (keys:FS.set k) : prop =
  forall (key:k). FS.mem key keys <==> Some? (m key)

(** Concrete hash table type *)
val ht (k:eqtype) (v:Type0) : Type0

(** Separation logic predicate: hash table models the given map with given key set *)
val is_ht (#k:eqtype) (#v:Type0) ([@@@mkey] h:ht k v) (m:pmap k v) (keys:FS.set k) : slprop

(** Create a new hash table with given capacity and hash function *)
fn create
  (#k:eqtype)
  (#v:Type0)
  (hashf:(k -> SZ.t))
  (initial_capacity:SZ.t{SZ.v initial_capacity > 0})
  returns h:ht k v
  ensures is_ht h empty_pmap FS.emptyset

(** Lookup a value by key *)
fn lookup
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (key:k)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
  preserves is_ht h m keys
  returns result:option v
  ensures pure (result == reveal m key)

(** Insert a key-value pair - requires space for new key if not present *)
fn insert
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (key:k)
  (value:v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
  requires is_ht h m keys
  requires pure (FS.mem key keys \/ SZ.fits (FS.cardinality keys + 1))
  ensures is_ht h (insert_pmap m key value) (FS.insert key keys)

(** Remove a key-value pair *)
fn remove
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (key:k)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
  requires is_ht h m keys
  returns removed:bool
  ensures is_ht h (remove_pmap m key) (FS.remove key keys)
  ensures pure (removed == Some? (reveal m key))

(** Get the number of entries *)
fn size
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
  preserves is_ht h m keys
  returns n:SZ.t
  ensures pure (SZ.v n == FS.cardinality keys)

(** Free the hash table *)
fn free
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
  requires is_ht h m keys

//////////////////////////////////////////////////////////////////////////////
// Iterator API
//////////////////////////////////////////////////////////////////////////////

(** Iterator type - abstract handle for iterating over hash table entries *)
val ht_iter (k:eqtype) (v:Type0) : Type0

(** Get the hash table pointer from an iterator *)
val ht_of (#k:eqtype) (#v:Type0) (it:ht_iter k v) : ht k v

(** Predicate for an iterator that borrows a hash table
    - `it`: the iterator handle  
    - `m`: the map contents of the hash table
    - `all_keys`: all keys in the hash table
    - `remaining`: the set of keys not yet visited
    Invariant: remaining ⊆ all_keys *)
val is_ht_iter (#k:eqtype) (#v:Type0) ([@@@mkey]it:ht_iter k v) 
               (m:erased (pmap k v))
               (all_keys:erased (FS.set k))
               (remaining:erased (FS.set k))
  : slprop

(** Create an iterator for a hash table
    The iterator borrows the table (doesn't consume it)
    Initially all keys are remaining *)
fn create_iter
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
  requires is_ht h m keys
  returns it:ht_iter k v
  ensures is_ht_iter it m keys keys
  ensures pure (ht_of it == h)

(** Check if there are more entries to iterate *)
fn iter_has_next
  (#k:eqtype)
  (#v:Type0)
  (it:ht_iter k v)
  (#m:erased (pmap k v))
  (#all_keys #remaining:erased (FS.set k))
  requires is_ht_iter it m all_keys remaining
  returns b:bool
  ensures is_ht_iter it m all_keys remaining ** 
          pure (b <==> FS.cardinality remaining > 0)

(** Get current key-value pair and advance to next
    Requires that iter_has_next returned true *)
fn iter_next
  (#k:eqtype)
  (#v:Type0)
  (it:ht_iter k v)
  (#m:erased (pmap k v))
  (#all_keys #remaining:erased (FS.set k))
  requires is_ht_iter it m all_keys remaining
  requires pure (FS.cardinality remaining > 0)
  returns p:(k & v)
  ensures exists* remaining'.
          is_ht_iter it m all_keys remaining' **
          pure (
            FS.mem (fst p) remaining /\
            remaining' == FS.remove (fst p) remaining /\
            Some (snd p) == reveal m (fst p)
          )

(** Finish iteration and return the hash table
    Can finish at any time (doesn't need to exhaust all elements) *)
fn finish_iter
  (#k:eqtype)
  (#v:Type0)
  (it:ht_iter k v)
  (#m:erased (pmap k v))
  (#all_keys #remaining:erased (FS.set k))
  requires is_ht_iter it m all_keys remaining
  returns h:ht k v
  ensures is_ht h m all_keys
  ensures pure (h == ht_of it)
