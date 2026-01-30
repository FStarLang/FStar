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
  requires emp
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
  requires is_ht h m keys
  returns result:option v
  ensures is_ht h m keys ** pure (result == reveal m key)

(** Insert a key-value pair - requires space for new key if not present *)
fn insert
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (key:k)
  (value:v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
  requires is_ht h m keys ** pure (FS.mem key keys \/ SZ.fits (FS.cardinality keys + 1))
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
  ensures is_ht h (remove_pmap m key) (FS.remove key keys) ** pure (removed == Some? (reveal m key))

(** Get the number of entries *)
fn size
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
  requires is_ht h m keys
  returns n:SZ.t
  ensures is_ht h m keys ** pure (SZ.v n == FS.cardinality keys)

(** Free the hash table *)
fn free
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
  requires is_ht h m keys
  ensures emp
