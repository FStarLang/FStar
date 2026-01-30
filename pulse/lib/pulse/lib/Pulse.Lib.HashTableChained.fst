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
module Seq = FStar.Seq
module List = FStar.List.Tot
module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module LL = Pulse.Lib.LinkedList
module LLI = Pulse.Lib.LinkedList.Iter
module OR = Pulse.Lib.OnRange
module T = Pulse.Lib.Trade.Util
module FE = FStar.FunctionalExtensionality
module FS = FStar.FiniteSet.Base
open Pulse.Lib.Trade { ( @==> ) }

//////////////////////////////////////////////////////////////////////////////
// Bucket Entry and Operations
//////////////////////////////////////////////////////////////////////////////

(** Bucket entry: key-value pair *)
noeq
type entry (k:eqtype) (v:Type0) = {
  ekey: k;
  evalue: v;
}

(** A bucket is a linked list of entries *)
let bucket (k:eqtype) (v:Type0) = LL.llist (entry k v)

(** Find entry in a bucket list *)
let rec find_in_bucket (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k) 
  : Tot (option v) (decreases entries) =
  match entries with
  | [] -> None
  | hd::tl -> if hd.ekey = key then Some hd.evalue else find_in_bucket tl key

(** Check if key exists in bucket *)
let rec key_in_bucket (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | hd::tl -> hd.ekey = key || key_in_bucket tl key

(** No duplicate keys in bucket *)
let rec no_dup_keys (#k:eqtype) (#v:Type0) (entries:list (entry k v))
  : Tot prop (decreases entries) =
  match entries with
  | [] -> True
  | hd::tl -> ~(key_in_bucket tl hd.ekey) /\ no_dup_keys tl

(** Insert/update entry in bucket list, returns (new_list, was_new_key) *)
let rec insert_in_bucket (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k) (value:v)
  : Tot (list (entry k v) & bool) (decreases entries) =
  match entries with
  | [] -> ([{ekey=key; evalue=value}], true)
  | hd::tl -> 
    if hd.ekey = key 
    then ({ekey=key; evalue=value}::tl, false)
    else let (tl', is_new) = insert_in_bucket tl key value in
         (hd::tl', is_new)

(** Remove entry from bucket list, returns (new_list, was_removed) *)
let rec remove_from_bucket (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k) 
  : Tot (list (entry k v) & bool) (decreases entries) =
  match entries with
  | [] -> ([], false)
  | hd::tl -> 
    if hd.ekey = key 
    then (tl, true)
    else let (tl', removed) = remove_from_bucket tl key in
         (hd::tl', removed)

(** Length of bucket *)
let bucket_length (#k:eqtype) (#v:Type0) (entries:list (entry k v)) : nat =
  List.length entries

(** Build pmap from a single bucket *)
let rec bucket_to_pmap (#k:eqtype) (#v:Type0) (entries:list (entry k v))
  : Tot (pmap k v) (decreases entries) =
  match entries with
  | [] -> empty_pmap
  | hd::tl -> insert_pmap (bucket_to_pmap tl) hd.ekey hd.evalue

(** Predicate: all keys in bucket hash to given index *)
let rec bucket_wf (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (hashf:k -> SZ.t) (capacity:pos) (idx:nat{idx < capacity})
  : Tot prop (decreases entries) =
  match entries with
  | [] -> True
  | hd::tl -> SZ.v (hashf hd.ekey) % capacity == idx /\ bucket_wf tl hashf capacity idx

//////////////////////////////////////////////////////////////////////////////
// Lemmas about bucket operations
//////////////////////////////////////////////////////////////////////////////

let rec find_insert_same (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k) (value:v)
  : Lemma (ensures find_in_bucket (fst (insert_in_bucket entries key value)) key == Some value)
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> if hd.ekey = key then () else find_insert_same tl key value

let rec find_insert_other (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k) (value:v) (key':k)
  : Lemma (requires key' <> key)
          (ensures find_in_bucket (fst (insert_in_bucket entries key value)) key' == find_in_bucket entries key')
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> if hd.ekey = key then () else find_insert_other tl key value key'

(** remove_from_bucket returns true iff key was in bucket *)
let rec remove_returns_key_in_bucket (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k)
  : Lemma (ensures snd (remove_from_bucket entries key) == key_in_bucket entries key)
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> if hd.ekey = key then () else remove_returns_key_in_bucket tl key

(** key_in_bucket is equivalent to find_in_bucket returning Some *)
let rec key_in_means_some (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k)
  : Lemma (ensures key_in_bucket entries key == Some? (find_in_bucket entries key))
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> if hd.ekey = key then () else key_in_means_some tl key

(** If key is not in bucket, find returns None *)
let rec key_not_in_means_none (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k)
  : Lemma (requires ~(key_in_bucket entries key))
          (ensures find_in_bucket entries key == None)
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> key_not_in_means_none tl key

(** Key equality: find_in_bucket and bucket_to_pmap give the same result *)
let rec find_equals_pmap (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k)
  : Lemma (ensures find_in_bucket entries key == bucket_to_pmap entries key)
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then ()
      else find_equals_pmap tl key

(** If key is not in bucket, pmap lookup returns None *)
let key_not_in_pmap_none (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k)
  : Lemma (requires ~(key_in_bucket entries key))
          (ensures bucket_to_pmap entries key == None)
  = key_not_in_means_none entries key;
    find_equals_pmap entries key

let rec find_remove_same (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k)
  : Lemma (requires no_dup_keys entries)
          (ensures find_in_bucket (fst (remove_from_bucket entries key)) key == None)
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then 
        key_not_in_means_none tl key  // key not in tl by no_dup_keys
      else 
        find_remove_same tl key  // key not at head, recurse

let rec find_remove_other (#k:eqtype) (#v:Type0) (entries:list (entry k v)) (key:k) (key':k)
  : Lemma (requires key' <> key)
          (ensures find_in_bucket (fst (remove_from_bucket entries key)) key' == find_in_bucket entries key')
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> if hd.ekey = key then () else find_remove_other tl key key'

let rec insert_preserves_wf (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (value:v) (hashf:k -> SZ.t) (capacity:pos) (idx:nat{idx < capacity})
  : Lemma (requires bucket_wf entries hashf capacity idx /\ SZ.v (hashf key) % capacity == idx)
          (ensures bucket_wf (fst (insert_in_bucket entries key value)) hashf capacity idx)
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> if hd.ekey = key then () else insert_preserves_wf tl key value hashf capacity idx

let rec remove_preserves_wf (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (hashf:k -> SZ.t) (capacity:pos) (idx:nat{idx < capacity})
  : Lemma (requires bucket_wf entries hashf capacity idx)
          (ensures bucket_wf (fst (remove_from_bucket entries key)) hashf capacity idx)
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> if hd.ekey = key then () else remove_preserves_wf tl key hashf capacity idx

(** Cons after remove preserves bucket_wf *)
let cons_after_remove_wf (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (value:v) (hashf:k -> SZ.t) (capacity:pos) (idx:nat{idx < capacity})
  : Lemma (requires bucket_wf entries hashf capacity idx /\ SZ.v (hashf key) % capacity == idx)
          (ensures bucket_wf ({ekey=key; evalue=value} :: (fst (remove_from_bucket entries key))) hashf capacity idx)
  = remove_preserves_wf entries key hashf capacity idx

(** Remove preserves key not in bucket for other keys *)
let rec remove_preserves_key_not_in (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (other:k)
  : Lemma 
    (requires ~(key_in_bucket entries other))
    (ensures ~(key_in_bucket (fst (remove_from_bucket entries key)) other))
    (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then ()  // After remove, just tl which doesn't have other
      else remove_preserves_key_not_in tl key other

(** Remove preserves no_dup_keys *)
let rec remove_preserves_no_dup (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k)
  : Lemma (requires no_dup_keys entries)
          (ensures no_dup_keys (fst (remove_from_bucket entries key)))
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then ()
      else begin
        // entries = hd::tl, result = hd :: remove(tl, key)
        // no_dup_keys entries means: ~(key_in_bucket tl hd.ekey) /\ no_dup_keys tl
        // We need: ~(key_in_bucket (remove(tl, key)) hd.ekey) /\ no_dup_keys (remove(tl, key))
        remove_preserves_no_dup tl key;
        remove_preserves_key_not_in tl key hd.ekey
      end

(** Key not in bucket after remove *)
let rec key_not_in_after_remove (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k)
  : Lemma (requires no_dup_keys entries)
          (ensures ~(key_in_bucket (fst (remove_from_bucket entries key)) key))
          (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then ()  // removed, rest doesn't have key (by no_dup_keys)
      else key_not_in_after_remove tl key

(** Cons after remove preserves no_dup_keys *)
let cons_after_remove_no_dup (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (value:v)
  : Lemma (requires no_dup_keys entries)
          (ensures no_dup_keys ({ekey=key; evalue=value} :: (fst (remove_from_bucket entries key))))
  = remove_preserves_no_dup entries key;
    key_not_in_after_remove entries key

//////////////////////////////////////////////////////////////////////////////
// Hash Table Representation
//////////////////////////////////////////////////////////////////////////////

(** Concrete hash table type *)
noeq
type ht_t (k:eqtype) (v:Type0) = {
  buckets: V.vec (bucket k v);
  count: B.box SZ.t;
  capacity: (c:SZ.t{SZ.v c > 0});
  hashf: k -> SZ.t;
}

let ht (k:eqtype) (v:Type0) = ht_t k v

//////////////////////////////////////////////////////////////////////////////
// Building the spec from bucket contents
//////////////////////////////////////////////////////////////////////////////

(** Build the full pmap from all buckets *)
let rec build_pmap_from_buckets (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (idx:nat)
  : Tot (pmap k v) (decreases (capacity - idx)) =
  if idx >= capacity then empty_pmap
  else 
    let rest = build_pmap_from_buckets bucket_contents hashf capacity (idx + 1) in
    let current = bucket_to_pmap (Seq.index bucket_contents idx) in
    FE.on_dom k (fun key ->
      if SZ.v (hashf key) % capacity = idx then current key
      else rest key)

(** Total count across all buckets *)
let rec total_count (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) (idx:nat)
  : Tot nat (decreases (Seq.length bucket_contents - idx)) =
  if idx >= Seq.length bucket_contents then 0
  else bucket_length (Seq.index bucket_contents idx) + total_count bucket_contents (idx + 1)

(** Build key set from a single bucket *)
let rec bucket_keys (#k:eqtype) (#v:Type0) (entries:list (entry k v))
  : GTot (FS.set k) (decreases entries) =
  match entries with
  | [] -> FS.emptyset
  | hd::tl -> FS.insert hd.ekey (bucket_keys tl)

(** Build key set from all buckets *)
let rec build_keys_from_buckets (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (idx:nat)
  : GTot (FS.set k) (decreases (Seq.length bucket_contents - idx)) =
  if idx >= Seq.length bucket_contents then FS.emptyset
  else FS.union (bucket_keys (Seq.index bucket_contents idx)) 
                (build_keys_from_buckets bucket_contents (idx + 1))

(** All buckets are well-formed *)
let rec all_buckets_wf (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (idx:nat)
  : Tot prop (decreases (capacity - idx)) =
  if idx >= capacity then True
  else bucket_wf (Seq.index bucket_contents idx) hashf capacity idx /\
       all_buckets_wf bucket_contents hashf capacity (idx + 1)

(** All buckets have no duplicate keys *)
let rec all_buckets_no_dup (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (idx:nat)
  : Tot prop (decreases (Seq.length bucket_contents - idx)) =
  if idx >= Seq.length bucket_contents then True
  else no_dup_keys (Seq.index bucket_contents idx) /\
       all_buckets_no_dup bucket_contents (idx + 1)

//////////////////////////////////////////////////////////////////////////////
// Key lemmas for lookup correctness
//////////////////////////////////////////////////////////////////////////////

(** Insert after remove of same key equals just insert *)
let insert_after_remove_same (#k:eqtype) (#v:Type0) (m:pmap k v) (key:k) (value:v)
  : Lemma (ensures insert_pmap (remove_pmap m key) key value == insert_pmap m key value)
  = let f1 = insert_pmap (remove_pmap m key) key value in
    let f2 = insert_pmap m key value in
    let aux (key':k) : Lemma (f1 key' == f2 key') = () in
    FStar.Classical.forall_intro aux;
    FE.extensionality k (fun _ -> option v) f1 f2

let rec build_pmap_correct (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (idx:nat)
  (key:k)
  : Lemma (ensures 
      build_pmap_from_buckets bucket_contents hashf capacity idx key ==
      (if SZ.v (hashf key) % capacity < idx then None
       else if SZ.v (hashf key) % capacity >= capacity then None
       else bucket_to_pmap (Seq.index bucket_contents (SZ.v (hashf key) % capacity)) key))
          (decreases (capacity - idx))
  = if idx >= capacity then ()
    else if SZ.v (hashf key) % capacity = idx then ()
    else build_pmap_correct bucket_contents hashf capacity (idx + 1) key

(** Main lookup correctness lemma *)
let lookup_correct (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k)
  : Lemma (ensures 
      build_pmap_from_buckets bucket_contents hashf capacity 0 key ==
      find_in_bucket (Seq.index bucket_contents (SZ.v (hashf key) % capacity)) key)
  = build_pmap_correct bucket_contents hashf capacity 0 key;
    find_equals_pmap (Seq.index bucket_contents (SZ.v (hashf key) % capacity)) key

(** Remove returns true iff key was in pmap *)
let remove_returns_some (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k)
  : Lemma (ensures 
      snd (remove_from_bucket (Seq.index bucket_contents (SZ.v (hashf key) % capacity)) key) ==
      Some? (build_pmap_from_buckets bucket_contents hashf capacity 0 key))
  = let idx = SZ.v (hashf key) % capacity in
    let entries = Seq.index bucket_contents idx in
    remove_returns_key_in_bucket entries key;
    key_in_means_some entries key;
    lookup_correct bucket_contents hashf capacity key

//////////////////////////////////////////////////////////////////////////////
// Lemmas for bucket update correctness
//////////////////////////////////////////////////////////////////////////////

(** Update a single bucket in the sequence *)
let update_bucket (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (idx:nat{idx < Seq.length bucket_contents})
  (new_entries:list (entry k v))
  : Seq.seq (list (entry k v)) =
  Seq.upd bucket_contents idx new_entries

(** build_pmap_from_buckets from idx only depends on buckets >= idx *)
let rec build_pmap_same_prefix (#k:eqtype) (#v:Type0) 
  (bc1 bc2:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bc1 /\ capacity == Seq.length bc2})
  (idx:nat)
  (update_idx:nat)
  (key:k)
  : Lemma 
    (requires idx > update_idx /\ (forall (j:nat). j >= idx /\ j < capacity ==> Seq.index bc1 j == Seq.index bc2 j))
    (ensures build_pmap_from_buckets bc1 hashf capacity idx key == build_pmap_from_buckets bc2 hashf capacity idx key)
    (decreases (capacity - idx))
  = if idx >= capacity then ()
    else begin
      build_pmap_same_prefix bc1 bc2 hashf capacity (idx + 1) update_idx key;
      assert (Seq.index bc1 idx == Seq.index bc2 idx)
    end

(** bucket_to_pmap respects insert *)
let rec bucket_pmap_insert (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (value:v) (key':k)
  : Lemma (ensures 
      bucket_to_pmap (fst (insert_in_bucket entries key value)) key' ==
      insert_pmap (bucket_to_pmap entries) key value key')
    (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then ()
      else bucket_pmap_insert tl key value key'

(** bucket_to_pmap respects remove *)
let rec bucket_pmap_remove (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (key':k)
  : Lemma (requires no_dup_keys entries)
    (ensures 
      bucket_to_pmap (fst (remove_from_bucket entries key)) key' ==
      remove_pmap (bucket_to_pmap entries) key key')
    (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then 
        // After removal, result is tl
        // LHS = bucket_to_pmap tl key'
        // RHS = remove_pmap (insert_pmap (bucket_to_pmap tl) key hd.evalue) key key'
        // When key' = key: RHS = None, LHS needs key_not_in_pmap_none
        // When key' <> key: RHS = insert_pmap (bucket_to_pmap tl) key hd.evalue key' = bucket_to_pmap tl key'
        if key' = key then key_not_in_pmap_none tl key
        else ()
      else bucket_pmap_remove tl key key'

(** Cons-after-remove gives same pmap as insert *)
let bucket_pmap_remove_cons (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (value:v) (key':k)
  : Lemma 
    (requires no_dup_keys entries)
    (ensures 
      bucket_to_pmap ({ekey=key; evalue=value} :: (fst (remove_from_bucket entries key))) key' ==
      insert_pmap (bucket_to_pmap entries) key value key')
  = let removed = fst (remove_from_bucket entries key) in
    // bucket_to_pmap ({key,value}::removed) = insert_pmap (bucket_to_pmap removed) key value
    // bucket_to_pmap removed = remove_pmap (bucket_to_pmap entries) key (by bucket_pmap_remove)
    // So LHS = insert_pmap (remove_pmap (bucket_to_pmap entries) key) key value
    //        = insert_pmap (bucket_to_pmap entries) key value  (by insert_after_remove_same)
    bucket_pmap_remove entries key key';
    insert_after_remove_same (bucket_to_pmap entries) key value

(** Full pmap equality for cons-after-remove *)
let bucket_pmap_remove_cons_full (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (value:v)
  : Lemma 
    (requires no_dup_keys entries)
    (ensures 
      bucket_to_pmap ({ekey=key; evalue=value} :: (fst (remove_from_bucket entries key))) ==
      insert_pmap (bucket_to_pmap entries) key value)
  = let f1 = bucket_to_pmap ({ekey=key; evalue=value} :: (fst (remove_from_bucket entries key))) in
    let f2 = insert_pmap (bucket_to_pmap entries) key value in
    let aux (k':k) : Lemma (f1 k' == f2 k') = bucket_pmap_remove_cons entries key value k' in
    FStar.Classical.forall_intro aux;
    FE.extensionality k (fun _ -> option v) f1 f2

(** Main insert correctness: updating bucket updates pmap correctly *)
let insert_bucket_correct (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k) (value:v) (key':k)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0)
    (ensures (
      let idx = SZ.v (hashf key) % capacity in
      let new_entries = fst (insert_in_bucket (Seq.index bucket_contents idx) key value) in
      let new_contents = update_bucket bucket_contents idx new_entries in
      build_pmap_from_buckets new_contents hashf capacity 0 key' ==
      insert_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key value key'
    ))
  = let idx = SZ.v (hashf key) % capacity in
    let old_entries = Seq.index bucket_contents idx in
    let new_entries = fst (insert_in_bucket old_entries key value) in
    let new_contents = update_bucket bucket_contents idx new_entries in
    let idx' = SZ.v (hashf key') % capacity in
    build_pmap_correct new_contents hashf capacity 0 key';
    build_pmap_correct bucket_contents hashf capacity 0 key';
    if idx' = idx then begin
      bucket_pmap_insert old_entries key value key';
      find_equals_pmap new_entries key';
      find_equals_pmap old_entries key'
    end else begin
      // Different bucket, unchanged
      assert (Seq.index new_contents idx' == Seq.index bucket_contents idx')
    end

(** Main insert correctness: full equality version *)
let insert_bucket_correct_full (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k) (value:v)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0)
    (ensures (
      let idx = SZ.v (hashf key) % capacity in
      let new_entries = fst (insert_in_bucket (Seq.index bucket_contents idx) key value) in
      let new_contents = update_bucket bucket_contents idx new_entries in
      build_pmap_from_buckets new_contents hashf capacity 0 ==
      insert_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key value
    ))
  = let idx = SZ.v (hashf key) % capacity in
    let old_entries = Seq.index bucket_contents idx in
    let new_entries = fst (insert_in_bucket old_entries key value) in
    let new_contents = update_bucket bucket_contents idx new_entries in
    let f1 = build_pmap_from_buckets new_contents hashf capacity 0 in
    let f2 = insert_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key value in
    let aux (key':k) : Lemma (f1 key' == f2 key') = 
      insert_bucket_correct bucket_contents hashf capacity key value key'
    in
    FStar.Classical.forall_intro aux;
    FE.extensionality k (fun _ -> option v) f1 f2

(** Cons-based insert: cons to front gives correct pmap (pointwise) *)
let cons_insert_pmap_correct (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k) (value:v) (key':k)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0)
    (ensures (
      let idx = SZ.v (hashf key) % capacity in
      let old_entries = Seq.index bucket_contents idx in
      let new_entries = {ekey=key; evalue=value} :: old_entries in
      let new_contents = Seq.upd bucket_contents idx new_entries in
      build_pmap_from_buckets new_contents hashf capacity 0 key' ==
      insert_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key value key'
    ))
  = let idx = SZ.v (hashf key) % capacity in
    let old_entries = Seq.index bucket_contents idx in
    let new_entries = {ekey=key; evalue=value} :: old_entries in
    let new_contents = Seq.upd bucket_contents idx new_entries in
    let idx' = SZ.v (hashf key') % capacity in
    build_pmap_correct new_contents hashf capacity 0 key';
    build_pmap_correct bucket_contents hashf capacity 0 key';
    if idx' = idx then begin
      // bucket_to_pmap ({key,value}::old_entries) = insert_pmap (bucket_to_pmap old_entries) key value
      // This is by definition of bucket_to_pmap
      find_equals_pmap new_entries key';
      find_equals_pmap old_entries key'
    end else begin
      // Different bucket, unchanged
      assert (Seq.index new_contents idx' == Seq.index bucket_contents idx')
    end

(** Cons-based insert: full equality *)
let cons_insert_pmap_correct_full (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k) (value:v)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0)
    (ensures (
      let idx = SZ.v (hashf key) % capacity in
      let old_entries = Seq.index bucket_contents idx in
      let new_entries = {ekey=key; evalue=value} :: old_entries in
      let new_contents = Seq.upd bucket_contents idx new_entries in
      build_pmap_from_buckets new_contents hashf capacity 0 ==
      insert_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key value
    ))
  = let idx = SZ.v (hashf key) % capacity in
    let old_entries = Seq.index bucket_contents idx in
    let new_entries = {ekey=key; evalue=value} :: old_entries in
    let new_contents = Seq.upd bucket_contents idx new_entries in
    let f1 = build_pmap_from_buckets new_contents hashf capacity 0 in
    let f2 = insert_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key value in
    let aux (key':k) : Lemma (f1 key' == f2 key') = 
      cons_insert_pmap_correct bucket_contents hashf capacity key value key'
    in
    FStar.Classical.forall_intro aux;
    FE.extensionality k (fun _ -> option v) f1 f2

(** Main remove correctness: updating bucket updates pmap correctly *)
let remove_bucket_correct (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k) (key':k)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0 /\
              no_dup_keys (Seq.index bucket_contents (SZ.v (hashf key) % capacity)))
    (ensures (
      let idx = SZ.v (hashf key) % capacity in
      let new_entries = fst (remove_from_bucket (Seq.index bucket_contents idx) key) in
      let new_contents = update_bucket bucket_contents idx new_entries in
      build_pmap_from_buckets new_contents hashf capacity 0 key' ==
      remove_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key key'
    ))
  = let idx = SZ.v (hashf key) % capacity in
    let old_entries = Seq.index bucket_contents idx in
    let new_entries = fst (remove_from_bucket old_entries key) in
    let new_contents = update_bucket bucket_contents idx new_entries in
    let idx' = SZ.v (hashf key') % capacity in
    build_pmap_correct new_contents hashf capacity 0 key';
    build_pmap_correct bucket_contents hashf capacity 0 key';
    if idx' = idx then begin
      bucket_pmap_remove old_entries key key';
      find_equals_pmap new_entries key';
      find_equals_pmap old_entries key'
    end else begin
      // Different bucket, unchanged
      assert (Seq.index new_contents idx' == Seq.index bucket_contents idx')
    end

(** Extract no_dup_keys from all_buckets_no_dup at a specific index *)
let rec all_buckets_no_dup_at_aux (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (start_idx:nat)
  (target_idx:nat{start_idx <= target_idx /\ target_idx < Seq.length bucket_contents})
  : Lemma 
    (requires all_buckets_no_dup bucket_contents start_idx)
    (ensures no_dup_keys (Seq.index bucket_contents target_idx))
    (decreases (target_idx - start_idx))
  = if start_idx = target_idx then ()
    else all_buckets_no_dup_at_aux bucket_contents (start_idx + 1) target_idx

let all_buckets_no_dup_at (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (idx:nat{idx < Seq.length bucket_contents})
  : Lemma 
    (requires all_buckets_no_dup bucket_contents 0)
    (ensures no_dup_keys (Seq.index bucket_contents idx))
  = all_buckets_no_dup_at_aux bucket_contents 0 idx

(** Full equality version of remove_bucket_correct using all_buckets_no_dup *)
let remove_bucket_correct_full (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0 /\
              all_buckets_no_dup bucket_contents 0)
    (ensures (
      let idx = SZ.v (hashf key) % capacity in
      let new_entries = fst (remove_from_bucket (Seq.index bucket_contents idx) key) in
      let new_contents = update_bucket bucket_contents idx new_entries in
      build_pmap_from_buckets new_contents hashf capacity 0 ==
      remove_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key
    ))
  = let idx = SZ.v (hashf key) % capacity in
    all_buckets_no_dup_at bucket_contents idx;
    let old_entries = Seq.index bucket_contents idx in
    let new_entries = fst (remove_from_bucket old_entries key) in
    let new_contents = update_bucket bucket_contents idx new_entries in
    let f1 = build_pmap_from_buckets new_contents hashf capacity 0 in
    let f2 = remove_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key in
    let aux (key':k) : Lemma (f1 key' == f2 key') = 
      remove_bucket_correct bucket_contents hashf capacity key key'
    in
    FStar.Classical.forall_intro aux;
    FE.extensionality k (fun _ -> option v) f1 f2

(** When key is not in any bucket, remove_pmap m key == m *)
let remove_pmap_absent (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0 /\
              ~(key_in_bucket (Seq.index bucket_contents (SZ.v (hashf key) % capacity)) key))
    (ensures (
      let m = build_pmap_from_buckets bucket_contents hashf capacity 0 in
      remove_pmap m key == m
    ))
  = let idx = SZ.v (hashf key) % capacity in
    let m = build_pmap_from_buckets bucket_contents hashf capacity 0 in
    // key_in_bucket is false for the bucket key hashes to
    // So bucket_to_pmap returns None at this key, meaning m key == None
    key_not_in_pmap_none (Seq.index bucket_contents idx) key;
    build_pmap_correct bucket_contents hashf capacity 0 key;
    // m key == bucket_to_pmap (Seq.index bucket_contents idx) key == None
    // Therefore remove_pmap m key == m (removing a key with value None doesn't change the map)
    let aux (key':k) : Lemma (remove_pmap m key key' == m key') = ()
    in
    FStar.Classical.forall_intro aux;
    FE.extensionality k (fun _ -> option v) (remove_pmap m key) m

(** Explicit version of remove_bucket_correct_full that takes new_contents as input *)
let remove_bucket_correct_full_explicit (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (new_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k)
  (m:pmap k v)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0 /\
              all_buckets_no_dup bucket_contents 0 /\
              m == build_pmap_from_buckets bucket_contents hashf capacity 0 /\
              (let idx = SZ.v (hashf key) % capacity in
               new_contents == update_bucket bucket_contents idx (fst (remove_from_bucket (Seq.index bucket_contents idx) key))))
    (ensures build_pmap_from_buckets new_contents hashf capacity 0 == remove_pmap m key)
  = remove_bucket_correct_full bucket_contents hashf capacity key

(** Cons-after-remove at buckets level: pmap equals insert_pmap *)
let remove_cons_insert_pmap_correct (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k) (value:v) (key':k)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0 /\
              all_buckets_no_dup bucket_contents 0)
    (ensures (
      let idx = SZ.v (hashf key) % capacity in
      let old_entries = Seq.index bucket_contents idx in
      let removed_entries = fst (remove_from_bucket old_entries key) in
      let new_entries = {ekey=key; evalue=value} :: removed_entries in
      let new_contents = Seq.upd bucket_contents idx new_entries in
      build_pmap_from_buckets new_contents hashf capacity 0 key' ==
      insert_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key value key'
    ))
  = let idx = SZ.v (hashf key) % capacity in
    let old_entries = Seq.index bucket_contents idx in
    let removed_entries = fst (remove_from_bucket old_entries key) in
    let new_entries = {ekey=key; evalue=value} :: removed_entries in
    let new_contents = Seq.upd bucket_contents idx new_entries in
    let idx' = SZ.v (hashf key') % capacity in
    build_pmap_correct new_contents hashf capacity 0 key';
    build_pmap_correct bucket_contents hashf capacity 0 key';
    all_buckets_no_dup_at bucket_contents idx;
    if idx' = idx then begin
      bucket_pmap_remove_cons old_entries key value key';
      find_equals_pmap new_entries key';
      find_equals_pmap old_entries key'
    end else begin
      assert (Seq.index new_contents idx' == Seq.index bucket_contents idx')
    end

(** Full equality version *)
let remove_cons_insert_pmap_correct_full (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k) (value:v)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0 /\
              all_buckets_no_dup bucket_contents 0)
    (ensures (
      let idx = SZ.v (hashf key) % capacity in
      let old_entries = Seq.index bucket_contents idx in
      let removed_entries = fst (remove_from_bucket old_entries key) in
      let new_entries = {ekey=key; evalue=value} :: removed_entries in
      let new_contents = Seq.upd bucket_contents idx new_entries in
      build_pmap_from_buckets new_contents hashf capacity 0 ==
      insert_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key value
    ))
  = let idx = SZ.v (hashf key) % capacity in
    let old_entries = Seq.index bucket_contents idx in
    let removed_entries = fst (remove_from_bucket old_entries key) in
    let new_entries = {ekey=key; evalue=value} :: removed_entries in
    let new_contents = Seq.upd bucket_contents idx new_entries in
    let f1 = build_pmap_from_buckets new_contents hashf capacity 0 in
    let f2 = insert_pmap (build_pmap_from_buckets bucket_contents hashf capacity 0) key value in
    let aux (key':k) : Lemma (f1 key' == f2 key') = 
      remove_cons_insert_pmap_correct bucket_contents hashf capacity key value key'
    in
    FStar.Classical.forall_intro aux;
    FE.extensionality k (fun _ -> option v) f1 f2

//////////////////////////////////////////////////////////////////////////////
// Lemmas for count and well-formedness after bucket update
//////////////////////////////////////////////////////////////////////////////

(** Empty buckets have no_dup_keys *)
let rec empty_buckets_no_dup (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (idx:nat)
  : Lemma 
    (requires forall (i:nat). i < Seq.length bucket_contents ==> Seq.index bucket_contents i == [])
    (ensures all_buckets_no_dup bucket_contents idx)
    (decreases (Seq.length bucket_contents - idx))
  = if idx >= Seq.length bucket_contents then ()
    else empty_buckets_no_dup bucket_contents (idx + 1)

(** Total count after cons: increases by 1 *)
let rec total_count_cons (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (new_entry:entry k v)
  (idx:nat)
  : Lemma 
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let new_entries = new_entry :: old_entries in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      total_count new_contents idx ==
      (if idx <= update_idx then total_count bucket_contents idx + 1
       else total_count bucket_contents idx)
    ))
    (decreases (Seq.length bucket_contents - idx))
  = let old_entries = Seq.index bucket_contents update_idx in
    let new_entries = new_entry :: old_entries in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= Seq.length bucket_contents then ()
    else if idx = update_idx then begin
      // At the updated index, length increases by 1
      total_count_cons bucket_contents update_idx new_entry (idx + 1)
    end else if idx < update_idx then begin
      // Before update_idx, unchanged but recurse adds 1
      total_count_cons bucket_contents update_idx new_entry (idx + 1)
    end else begin
      // After update_idx, unchanged
      total_count_cons bucket_contents update_idx new_entry (idx + 1)
    end

(** Extract bucket_wf from all_buckets_wf - helper that walks from start *)
let rec all_buckets_wf_at_aux (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (hashf:k -> SZ.t)
  (capacity:pos{capacity == Seq.length bucket_contents})
  (start:nat)
  (idx:nat{idx < capacity})
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity start /\ start <= idx)
    (ensures bucket_wf (Seq.index bucket_contents idx) hashf capacity idx)
    (decreases idx - start)
  = if start = idx then ()
    else all_buckets_wf_at_aux bucket_contents hashf capacity (start + 1) idx

(** Extract bucket_wf from all_buckets_wf *)
let all_buckets_wf_at (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (hashf:k -> SZ.t)
  (capacity:pos{capacity == Seq.length bucket_contents})
  (idx:nat{idx < capacity})
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0)
    (ensures bucket_wf (Seq.index bucket_contents idx) hashf capacity idx)
  = all_buckets_wf_at_aux bucket_contents hashf capacity 0 idx

(** All buckets wf after cons: if new entry hashes correctly, still wf *)
let rec all_buckets_wf_cons (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (hashf:k -> SZ.t)
  (capacity:pos{capacity == Seq.length bucket_contents})
  (update_idx:nat{update_idx < capacity})
  (new_entry:entry k v)
  (idx:nat)
  : Lemma 
    (requires 
      all_buckets_wf bucket_contents hashf capacity 0 /\
      SZ.v (hashf new_entry.ekey) % capacity == update_idx)
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let new_entries = new_entry :: old_entries in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      all_buckets_wf new_contents hashf capacity idx
    ))
    (decreases (capacity - idx))
  = let old_entries = Seq.index bucket_contents update_idx in
    let new_entries = new_entry :: old_entries in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= capacity then ()
    else begin
      if idx = update_idx then begin
        // At the updated index: need to show bucket_wf new_entries hashf capacity idx
        // new_entries = new_entry :: old_entries
        // bucket_wf requires: hash(new_entry.ekey) % capacity == idx (we have this)
        //                     bucket_wf old_entries hashf capacity idx
        all_buckets_wf_at bucket_contents hashf capacity idx;
        assert (bucket_wf old_entries hashf capacity idx)
      end else begin
        // At other indices: unchanged
        all_buckets_wf_at bucket_contents hashf capacity idx;
        assert (Seq.index new_contents idx == Seq.index bucket_contents idx)
      end;
      all_buckets_wf_cons bucket_contents hashf capacity update_idx new_entry (idx + 1)
    end

(** All buckets no_dup after cons following remove: if we remove then cons with same key *)
let rec all_buckets_no_dup_remove_cons (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k)
  (value:v)
  (idx:nat)
  : Lemma 
    (requires all_buckets_no_dup bucket_contents 0)
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let removed_entries = fst (remove_from_bucket old_entries key) in
      let new_entries = {ekey=key; evalue=value} :: removed_entries in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      all_buckets_no_dup new_contents idx
    ))
    (decreases (Seq.length bucket_contents - idx))
  = let old_entries = Seq.index bucket_contents update_idx in
    let removed_entries = fst (remove_from_bucket old_entries key) in
    let new_entries = {ekey=key; evalue=value} :: removed_entries in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= Seq.length bucket_contents then ()
    else begin
      if idx = update_idx then begin
        // At updated index: show no_dup_keys new_entries
        all_buckets_no_dup_at bucket_contents update_idx;
        cons_after_remove_no_dup old_entries key value
      end else begin
        // At other indices: unchanged
        all_buckets_no_dup_at bucket_contents idx;
        assert (Seq.index new_contents idx == Seq.index bucket_contents idx)
      end;
      all_buckets_no_dup_remove_cons bucket_contents update_idx key value (idx + 1)
    end

(** All buckets wf after remove then cons with same key *)
let rec all_buckets_wf_remove_cons (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (hashf:k -> SZ.t)
  (capacity:pos{capacity == Seq.length bucket_contents})
  (update_idx:nat{update_idx < capacity})
  (key:k)
  (value:v)
  (idx:nat)
  : Lemma 
    (requires 
      all_buckets_wf bucket_contents hashf capacity 0 /\
      SZ.v (hashf key) % capacity == update_idx)
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let removed_entries = fst (remove_from_bucket old_entries key) in
      let new_entries = {ekey=key; evalue=value} :: removed_entries in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      all_buckets_wf new_contents hashf capacity idx
    ))
    (decreases (capacity - idx))
  = let old_entries = Seq.index bucket_contents update_idx in
    let removed_entries = fst (remove_from_bucket old_entries key) in
    let new_entries = {ekey=key; evalue=value} :: removed_entries in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= capacity then ()
    else begin
      if idx = update_idx then begin
        // At updated index: show bucket_wf new_entries hashf capacity idx
        all_buckets_wf_at bucket_contents hashf capacity update_idx;
        cons_after_remove_wf old_entries key value hashf capacity idx
      end else begin
        // At other indices: unchanged
        all_buckets_wf_at bucket_contents hashf capacity idx;
        assert (Seq.index new_contents idx == Seq.index bucket_contents idx)
      end;
      all_buckets_wf_remove_cons bucket_contents hashf capacity update_idx key value (idx + 1)
    end

(** remove_from_bucket preserves or decreases bucket length *)
let rec remove_from_bucket_length (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k)
  : Lemma 
    (ensures (
      let (new_entries, removed) = remove_from_bucket entries key in
      List.length new_entries == (if removed then List.length entries - 1 else List.length entries)
    ))
    (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then ()
      else remove_from_bucket_length tl key

(** Total count after remove: decreases by 1 if entry was found *)
let rec total_count_remove (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k)
  (idx:nat)
  : Lemma 
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let (new_entries, removed) = remove_from_bucket old_entries key in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      total_count new_contents idx ==
      (if idx <= update_idx && removed then total_count bucket_contents idx - 1
       else total_count bucket_contents idx)
    ))
    (decreases (Seq.length bucket_contents - idx))
  = let old_entries = Seq.index bucket_contents update_idx in
    let (new_entries, removed) = remove_from_bucket old_entries key in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    remove_from_bucket_length old_entries key;
    if idx >= Seq.length bucket_contents then ()
    else if idx = update_idx then begin
      total_count_remove bucket_contents update_idx key (idx + 1)
    end else if idx < update_idx then begin
      total_count_remove bucket_contents update_idx key (idx + 1)
    end else begin
      total_count_remove bucket_contents update_idx key (idx + 1)
    end

(** Total count after remove-then-cons: net change is 0 if removed, +1 if not *)
let rec total_count_remove_cons (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k)
  (value:v)
  (idx:nat)
  : Lemma 
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let (removed_entries, was_removed) = remove_from_bucket old_entries key in
      let new_entries = {ekey=key; evalue=value} :: removed_entries in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      total_count new_contents idx ==
      (if idx <= update_idx then
         (if was_removed then total_count bucket_contents idx
          else total_count bucket_contents idx + 1)
       else total_count bucket_contents idx)
    ))
    (decreases (Seq.length bucket_contents - idx))
  = let old_entries = Seq.index bucket_contents update_idx in
    let (removed_entries, was_removed) = remove_from_bucket old_entries key in
    let new_entries = {ekey=key; evalue=value} :: removed_entries in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    remove_from_bucket_length old_entries key;
    if idx >= Seq.length bucket_contents then ()
    else if idx = update_idx then begin
      // At update_idx: bucket_length changes
      // len(new_entries) = len(removed_entries) + 1
      // len(removed_entries) = len(old_entries) - (if was_removed then 1 else 0)
      // So len(new_entries) = len(old_entries) + (if was_removed then 0 else 1)
      total_count_remove_cons bucket_contents update_idx key value (idx + 1)
    end else if idx < update_idx then begin
      // Before update_idx: same bucket_length, but recursion adds the difference
      total_count_remove_cons bucket_contents update_idx key value (idx + 1)
    end else begin
      // After update_idx: same
      total_count_remove_cons bucket_contents update_idx key value (idx + 1)
    end

(** Convenient version starting from 0 *)
let total_count_remove_cons_full (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k)
  (value:v)
  : Lemma 
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let (removed_entries, was_removed) = remove_from_bucket old_entries key in
      let new_entries = {ekey=key; evalue=value} :: removed_entries in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      total_count new_contents 0 ==
      (if was_removed then total_count bucket_contents 0
       else total_count bucket_contents 0 + 1)
    ))
  = total_count_remove_cons bucket_contents update_idx key value 0

(** remove_from_bucket preserves bucket_wf *)
let rec remove_preserves_bucket_wf (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k) (hashf:k -> SZ.t) (capacity:pos) (idx:nat{idx < capacity})
  : Lemma 
    (requires bucket_wf entries hashf capacity idx)
    (ensures bucket_wf (fst (remove_from_bucket entries key)) hashf capacity idx)
    (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then ()
      else remove_preserves_bucket_wf tl key hashf capacity idx

(** All buckets wf after remove: still wf *)
let rec all_buckets_wf_remove (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (hashf:k -> SZ.t)
  (capacity:pos{capacity == Seq.length bucket_contents})
  (update_idx:nat{update_idx < capacity})
  (key:k)
  (idx:nat)
  : Lemma 
    (requires all_buckets_wf bucket_contents hashf capacity 0)
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let new_entries = fst (remove_from_bucket old_entries key) in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      all_buckets_wf new_contents hashf capacity idx
    ))
    (decreases (capacity - idx))
  = let old_entries = Seq.index bucket_contents update_idx in
    let new_entries = fst (remove_from_bucket old_entries key) in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= capacity then ()
    else begin
      if idx = update_idx then begin
        all_buckets_wf_at bucket_contents hashf capacity idx;
        remove_preserves_bucket_wf old_entries key hashf capacity idx
      end else begin
        all_buckets_wf_at bucket_contents hashf capacity idx;
        assert (Seq.index new_contents idx == Seq.index bucket_contents idx)
      end;
      all_buckets_wf_remove bucket_contents hashf capacity update_idx key (idx + 1)
    end

(** All buckets no_dup after remove: still no_dup *)
let rec all_buckets_no_dup_remove (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k)
  (idx:nat)
  : Lemma 
    (requires all_buckets_no_dup bucket_contents 0)
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let new_entries = fst (remove_from_bucket old_entries key) in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      all_buckets_no_dup new_contents idx
    ))
    (decreases (Seq.length bucket_contents - idx))
  = let old_entries = Seq.index bucket_contents update_idx in
    let new_entries = fst (remove_from_bucket old_entries key) in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= Seq.length bucket_contents then ()
    else begin
      if idx = update_idx then begin
        all_buckets_no_dup_at bucket_contents update_idx;
        remove_preserves_no_dup old_entries key
      end else begin
        all_buckets_no_dup_at bucket_contents idx;
        assert (Seq.index new_contents idx == Seq.index bucket_contents idx)
      end;
      all_buckets_no_dup_remove bucket_contents update_idx key (idx + 1)
    end

//////////////////////////////////////////////////////////////////////////////
// Separation Logic Predicates
//////////////////////////////////////////////////////////////////////////////

(** Ownership of bucket at index i *)
let bucket_at (#k:eqtype) (#v:Type0) 
  (bucket_ptrs:Seq.seq (bucket k v)) 
  (bucket_contents:Seq.seq (list (entry k v)))
  (i:nat)
  : slprop =
  if i >= Seq.length bucket_ptrs || i >= Seq.length bucket_contents then emp
  else LL.is_list (Seq.index bucket_ptrs i) (Seq.index bucket_contents i)

(** The main hash table invariant *)
let is_ht (#k:eqtype) (#v:Type0) (h:ht k v) (m:pmap k v) (keys:FS.set k) : slprop =
  exists* (bucket_ptrs:Seq.seq (bucket k v)) 
         (bucket_contents:Seq.seq (list (entry k v))) 
         (cnt:SZ.t).
    V.pts_to h.buckets bucket_ptrs **
    B.pts_to h.count cnt **
    OR.on_range (bucket_at bucket_ptrs bucket_contents) 0 (SZ.v h.capacity) **
    pure (
      Seq.length bucket_ptrs == SZ.v h.capacity /\
      Seq.length bucket_contents == SZ.v h.capacity /\
      SZ.v cnt == total_count bucket_contents 0 /\
      all_buckets_wf bucket_contents h.hashf (SZ.v h.capacity) 0 /\
      all_buckets_no_dup bucket_contents 0 /\
      V.is_full_vec h.buckets /\
      m == build_pmap_from_buckets bucket_contents h.hashf (SZ.v h.capacity) 0 /\
      keys == build_keys_from_buckets bucket_contents 0 /\
      SZ.v cnt == FS.cardinality keys
    )

//////////////////////////////////////////////////////////////////////////////
// Lemmas for bucket_at and on_range manipulation
//////////////////////////////////////////////////////////////////////////////

(** Get bucket_at for a specific index from on_range, with trade to put it back *)
ghost
fn get_bucket_at (#k:eqtype) (#v:Type0)
  (bucket_ptrs:Seq.seq (bucket k v))
  (bucket_contents:Seq.seq (list (entry k v)))
  (lo hi:nat)
  (i:nat{lo <= i /\ i < hi})
requires 
  OR.on_range (bucket_at bucket_ptrs bucket_contents) lo hi **
  pure (hi <= Seq.length bucket_ptrs /\ hi <= Seq.length bucket_contents)
ensures 
  bucket_at bucket_ptrs bucket_contents i **
  (bucket_at bucket_ptrs bucket_contents i @==> 
   OR.on_range (bucket_at bucket_ptrs bucket_contents) lo hi)
{
  OR.on_range_focus i
}

(** Put back bucket_at into on_range using the trade *)
ghost
fn put_bucket_at (#k:eqtype) (#v:Type0)
  (bucket_ptrs:Seq.seq (bucket k v))
  (bucket_contents:Seq.seq (list (entry k v)))
  (lo hi:nat)
  (i:nat{lo <= i /\ i < hi})
requires 
  bucket_at bucket_ptrs bucket_contents i **
  (bucket_at bucket_ptrs bucket_contents i @==> 
   OR.on_range (bucket_at bucket_ptrs bucket_contents) lo hi)
ensures 
  OR.on_range (bucket_at bucket_ptrs bucket_contents) lo hi
{
  T.elim 
    (bucket_at bucket_ptrs bucket_contents i)
    (OR.on_range (bucket_at bucket_ptrs bucket_contents) lo hi)
}

//////////////////////////////////////////////////////////////////////////////
// Helper: unfold bucket_at when index is in range
//////////////////////////////////////////////////////////////////////////////

ghost
fn unfold_bucket_at (#k:eqtype) (#v:Type0)
  (bucket_ptrs:Seq.seq (bucket k v))
  (bucket_contents:Seq.seq (list (entry k v)))
  (i:nat{i < Seq.length bucket_ptrs /\ i < Seq.length bucket_contents})
requires 
  bucket_at bucket_ptrs bucket_contents i
ensures 
  LL.is_list (Seq.index bucket_ptrs i) (Seq.index bucket_contents i)
{
  rewrite (bucket_at bucket_ptrs bucket_contents i)
       as (LL.is_list (Seq.index bucket_ptrs i) (Seq.index bucket_contents i))
}

ghost
fn fold_bucket_at (#k:eqtype) (#v:Type0)
  (bucket_ptrs:Seq.seq (bucket k v))
  (bucket_contents:Seq.seq (list (entry k v)))
  (i:nat{i < Seq.length bucket_ptrs /\ i < Seq.length bucket_contents})
requires 
  LL.is_list (Seq.index bucket_ptrs i) (Seq.index bucket_contents i)
ensures 
  bucket_at bucket_ptrs bucket_contents i
{
  rewrite (LL.is_list (Seq.index bucket_ptrs i) (Seq.index bucket_contents i))
       as (bucket_at bucket_ptrs bucket_contents i)
}

//////////////////////////////////////////////////////////////////////////////
// Helper: Search a bucket for a key using recursive traversal
//////////////////////////////////////////////////////////////////////////////

(** Search a bucket for a key, returning the value if found *)
fn rec search_bucket_rec
  (#k:eqtype)
  (#v:Type0)
  (b:bucket k v)
  (key:k)
  (#entries:erased (list (entry k v)))
requires LL.is_list b entries
returns result:option v
ensures LL.is_list b entries ** pure (result == find_in_bucket entries key)
decreases entries
{
  let is_emp = LL.is_empty b;
  if is_emp {
    None #v
  } else {
    // Get the head and check
    let e = LL.head b;
    let ekey = e.ekey;
    let found_key = (ekey = key);
    if found_key {
      Some e.evalue
    } else {
      // Move to tail with trade
      let tail = LL.move_next b;
      with tl. _;
      
      // Recursively search tail
      let result = search_bucket_rec tail key;
      
      // Restore original list using the trade
      T.elim (LL.is_list tail tl) (LL.is_list b entries);
      
      result
    }
  }
}

//////////////////////////////////////////////////////////////////////////////
// Helper: Free all entries in a bucket
//////////////////////////////////////////////////////////////////////////////

(** Free all entries in a bucket by repeatedly popping *)
fn rec free_bucket
  (#k:eqtype)
  (#v:Type0)
  (b:bucket k v)
  (#entries:erased (list (entry k v)))
requires LL.is_list b entries
ensures emp
decreases entries
{
  let is_emp = LL.is_empty b;
  if is_emp {
    // Empty list: is_list null [] = pure (b == None), which is emp
    drop_ (LL.is_list b entries)
  } else {
    // Pop the head (which frees the node) and recurse
    let (tail, _) = LL.pop b;
    free_bucket tail
  }
}

//////////////////////////////////////////////////////////////////////////////
// Helper: Remove entry from bucket by key
//////////////////////////////////////////////////////////////////////////////

(** Remove the first entry with matching key from bucket *)
fn rec remove_from_bucket_fn
  (#k:eqtype)
  (#v:Type0)
  (b:bucket k v)
  (key:k)
  (#entries:erased (list (entry k v)))
requires LL.is_list b entries
returns result:(bucket k v & bool)
ensures LL.is_list (fst result) (fst (remove_from_bucket entries key)) ** 
        pure (snd result == snd (remove_from_bucket entries key))
decreases entries
{
  let is_emp = LL.is_empty b;
  if is_emp {
    // Empty list: nothing to remove
    (b, false)
  } else {
    // Check the head
    let e = LL.head b;
    let ekey = e.ekey;
    let found_key = (ekey = key);
    if found_key {
      // Found it: pop the head and return tail
      let (tail, _) = LL.pop b;
      (tail, true)
    } else {
      // Not found at head: pop, recurse on tail, cons back
      let (tail, hd) = LL.pop b;
      let (new_tail, removed) = remove_from_bucket_fn tail key;
      let result = LL.cons hd new_tail;
      (result, removed)
    }
  }
}

//////////////////////////////////////////////////////////////////////////////
// Create
//////////////////////////////////////////////////////////////////////////////

(** Safe indexing that returns option *)
let seq_index_opt (#a:Type) (s:Seq.seq a) (i:nat) : option a =
  if i < Seq.length s then Some (Seq.index s i) else None

(** Lemma: all empty buckets are well-formed *)
let rec all_empty_buckets_wf (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (idx:nat)
  : Lemma 
    (requires forall (j:nat). j < capacity ==> Seq.index bucket_contents j == [])
    (ensures all_buckets_wf bucket_contents hashf capacity idx)
    (decreases (capacity - idx))
  = if idx >= capacity then ()
    else all_empty_buckets_wf bucket_contents hashf capacity (idx + 1)

(** Lemma: empty buckets build to empty pmap (pointwise) *)
let rec empty_buckets_empty_pmap (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  (idx:nat)
  (key:k)
  : Lemma 
    (requires forall (j:nat). j < capacity ==> Seq.index bucket_contents j == [])
    (ensures build_pmap_from_buckets bucket_contents hashf capacity idx key == None)
    (decreases (capacity - idx))
  = if idx >= capacity then ()
    else empty_buckets_empty_pmap bucket_contents hashf capacity (idx + 1) key

(** Lemma: empty buckets build to empty pmap (full equality) *)
let empty_buckets_equal_empty_pmap (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (hashf:k -> SZ.t) 
  (capacity:pos{capacity == Seq.length bucket_contents})
  : Lemma 
    (requires forall (j:nat). j < capacity ==> Seq.index bucket_contents j == [])
    (ensures build_pmap_from_buckets bucket_contents hashf capacity 0 == empty_pmap #k #v)
  = let f1 = build_pmap_from_buckets bucket_contents hashf capacity 0 in
    let f2 = empty_pmap #k #v in
    let aux (key:k) : Lemma (f1 key == f2 key) = 
      empty_buckets_empty_pmap bucket_contents hashf capacity 0 key
    in
    FStar.Classical.forall_intro aux;
    FE.extensionality k (fun _ -> option v) f1 f2

(** Lemma: empty buckets have zero total count *)
let rec empty_buckets_zero_count (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (idx:nat)
  : Lemma 
    (requires forall (j:nat). idx <= j /\ j < Seq.length bucket_contents ==> Seq.index bucket_contents j == [])
    (ensures total_count bucket_contents idx == 0)
    (decreases (Seq.length bucket_contents - idx))
  = if idx >= Seq.length bucket_contents then ()
    else empty_buckets_zero_count bucket_contents (idx + 1)

(** Empty buckets build to empty key set *)
let rec empty_buckets_keys (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (idx:nat)
  : Lemma 
    (requires forall (j:nat). idx <= j /\ j < Seq.length bucket_contents ==> Seq.index bucket_contents j == [])
    (ensures build_keys_from_buckets bucket_contents idx == FS.emptyset)
    (decreases (Seq.length bucket_contents - idx))
  = FS.all_finite_set_facts_lemma ();
    if idx >= Seq.length bucket_contents then ()
    else begin
      empty_buckets_keys bucket_contents (idx + 1);
      // bucket_keys [] = emptyset, rest = emptyset
      // union emptyset emptyset = emptyset via membership
      let s1 = bucket_keys #k #v [] in
      let s2 = build_keys_from_buckets bucket_contents (idx + 1) in
      let result = FS.union s1 s2 in
      // Prove equal by showing membership equality
      assert (forall (x:k). FS.mem x s1 <==> false);  // emptyset contains nothing
      assert (forall (x:k). FS.mem x s2 <==> false);  // emptyset contains nothing  
      assert (forall (x:k). FS.mem x result <==> FS.mem x s1 \/ FS.mem x s2);  // union definition
      assert (forall (x:k). FS.mem x result <==> false);  // combined
      assert (forall (x:k). FS.mem x result <==> FS.mem x FS.emptyset);
      // Now use equal_fact and equal_extensionality_fact
      assert (FS.equal result FS.emptyset)
    end

(** Empty keys have cardinality 0 *)
let empty_keys_cardinality (#k:eqtype) (#v:Type0) 
  (bucket_contents:Seq.seq (list (entry k v))) 
  (idx:nat)
  : Lemma 
    (requires forall (j:nat). idx <= j /\ j < Seq.length bucket_contents ==> Seq.index bucket_contents j == [])
    (ensures FS.cardinality (build_keys_from_buckets bucket_contents idx) == 0)
  = empty_buckets_keys bucket_contents idx;
    FS.all_finite_set_facts_lemma ()

//////////////////////////////////////////////////////////////////////////////
// Key set lemmas for insert and remove
//////////////////////////////////////////////////////////////////////////////

(** Key not in bucket implies not in bucket_keys *)
let rec key_not_in_bucket_implies_not_in_keys (#k:eqtype) (#v:Type0)
  (entries:list (entry k v)) (key:k)
  : Lemma
    (requires ~(key_in_bucket entries key))
    (ensures ~(FS.mem key (bucket_keys entries)))
    (decreases entries)
  = FS.all_finite_set_facts_lemma ();
    match entries with
    | [] -> ()
    | hd::tl -> key_not_in_bucket_implies_not_in_keys tl key

(** Helper: if no_dup_keys (hd::tl) and hd.ekey = key, then key not in tl *)
let key_not_in_tl_means_not_in_keys (#k:eqtype) (#v:Type0)
  (entries:list (entry k v)) (key:k)
  : Lemma
    (requires no_dup_keys entries /\ (match entries with | [] -> False | hd::tl -> hd.ekey = key))
    (ensures (match entries with | [] -> True | hd::tl -> ~(FS.mem key (bucket_keys tl))))
  = FS.all_finite_set_facts_lemma ();
    match entries with
    | [] -> ()
    | hd::tl ->
      // no_dup_keys (hd::tl) means ~(key_in_bucket tl hd.ekey) /\ no_dup_keys tl
      // Since hd.ekey = key, ~(key_in_bucket tl key)
      key_not_in_bucket_implies_not_in_keys tl key

(** bucket_keys after remove_from_bucket: the removed key is gone (requires no_dup_keys) *)
let rec bucket_keys_after_remove (#k:eqtype) (#v:Type0) 
  (entries:list (entry k v)) (key:k)
  : Lemma 
    (requires no_dup_keys entries)
    (ensures bucket_keys (fst (remove_from_bucket entries key)) == 
             FS.remove key (bucket_keys entries))
    (decreases entries)
  = FS.all_finite_set_facts_lemma ();
    match entries with
    | [] -> 
      // Both sides are emptyset
      let empty : list (entry k v) = [] in
      assert (FS.equal (bucket_keys (fst (remove_from_bucket empty key))) (FS.remove key (bucket_keys empty)))
    | hd::tl ->
      if hd.ekey = key then begin
        // remove_from_bucket returns (tl, true)
        // bucket_keys entries = insert key (bucket_keys tl)
        // FS.remove key (insert key (bucket_keys tl))
        // Since no_dup_keys: key not in tl, so bucket_keys tl doesn't contain key
        let lhs = bucket_keys (fst (remove_from_bucket entries key)) in
        let rhs = FS.remove key (bucket_keys entries) in
        // lhs = bucket_keys tl
        // rhs = FS.remove key (FS.insert key (bucket_keys tl))
        // Since no_dup_keys (hd::tl), key not in tl
        // So bucket_keys tl doesn't contain key
        // Then remove key (insert key s) = s when key not in s
        key_not_in_tl_means_not_in_keys entries key;
        // Now we know: ~(FS.mem key (bucket_keys tl))
        // So remove key (insert key (bucket_keys tl)) = bucket_keys tl
        let s = bucket_keys tl in
        assert (forall (x:k). FS.mem x lhs <==> FS.mem x s);
        assert (forall (x:k). FS.mem x rhs <==> (x = key \/ FS.mem x s) /\ x <> key);
        assert (forall (x:k). FS.mem x rhs <==> FS.mem x s /\ x <> key);
        // Since key not in s: FS.mem x s /\ x <> key <==> FS.mem x s
        assert (forall (x:k). FS.mem x s ==> x <> key);
        assert (forall (x:k). FS.mem x rhs <==> FS.mem x s);
        assert (FS.equal lhs rhs)
      end else begin
        bucket_keys_after_remove tl key;
        // lhs = insert hd.ekey (bucket_keys (fst (remove_from_bucket tl key)))
        // By IH: bucket_keys (fst (remove_from_bucket tl key)) = FS.remove key (bucket_keys tl)
        // So lhs = insert hd.ekey (FS.remove key (bucket_keys tl))
        // rhs = FS.remove key (bucket_keys entries)
        //     = FS.remove key (insert hd.ekey (bucket_keys tl))
        // We need: insert hd.ekey (remove key s) = remove key (insert hd.ekey s) when hd.ekey <> key
        let s = bucket_keys tl in
        let lhs = FS.insert hd.ekey (FS.remove key s) in
        let rhs = FS.remove key (FS.insert hd.ekey s) in
        assert (forall (x:k). FS.mem x lhs <==> x = hd.ekey \/ (FS.mem x s /\ x <> key));
        assert (forall (x:k). FS.mem x rhs <==> (x = hd.ekey \/ FS.mem x s) /\ x <> key);
        assert (forall (x:k). FS.mem x rhs <==> (x = hd.ekey /\ x <> key) \/ (FS.mem x s /\ x <> key));
        // Since hd.ekey <> key: x = hd.ekey /\ x <> key iff x = hd.ekey
        assert (forall (x:k). FS.mem x rhs <==> x = hd.ekey \/ (FS.mem x s /\ x <> key));
        assert (FS.equal lhs rhs)
      end

(** bucket_keys after cons: adds the key *)
let bucket_keys_after_cons (#k:eqtype) (#v:Type0) 
  (e:entry k v) (entries:list (entry k v))
  : Lemma 
    (ensures bucket_keys (e :: entries) == FS.insert e.ekey (bucket_keys entries))
  = ()  // Direct from definition

(** Cons after remove: if no_dup_keys, result is insert on original keys *)
let rec bucket_keys_cons_after_remove (#k:eqtype) (#v:Type0)
  (entries:list (entry k v)) (key:k) (value:v)
  : Lemma
    (requires no_dup_keys entries)
    (ensures bucket_keys ({ekey=key; evalue=value} :: fst (remove_from_bucket entries key)) ==
             FS.insert key (bucket_keys entries))
    (decreases entries)
  = FS.all_finite_set_facts_lemma ();
    let new_entry = {ekey=key; evalue=value} in
    let removed = fst (remove_from_bucket entries key) in
    let lhs = bucket_keys (new_entry :: removed) in
    let rhs = FS.insert key (bucket_keys entries) in
    match entries with
    | [] ->
      // Both sides equal insert key emptyset
      ()
    | hd::tl ->
      if hd.ekey = key then begin
        // removed = tl, lhs = insert key (bucket_keys tl)
        // bucket_keys entries = insert key (bucket_keys tl)
        // rhs = insert key (insert key (bucket_keys tl)) = insert key (bucket_keys tl)
        assert (FS.equal lhs rhs)
      end else begin
        // removed = hd :: fst (remove_from_bucket tl key)
        // bucket_keys removed = insert hd.ekey (bucket_keys (fst (remove_from_bucket tl key)))
        // lhs = insert key (insert hd.ekey (bucket_keys (fst (remove_from_bucket tl key))))
        // rhs = insert key (insert hd.ekey (bucket_keys tl))
        // By no_dup_keys: key not in tl (since hd.ekey <> key and no_dup_keys entries)
        // Actually no_dup_keys (hd::tl) means hd.ekey not in tl AND no_dup_keys tl
        // But key might still be in tl
        bucket_keys_cons_after_remove tl key value;
        // IH: bucket_keys (new_entry :: fst (remove_from_bucket tl key)) = insert key (bucket_keys tl)
        let inner = bucket_keys (new_entry :: fst (remove_from_bucket tl key)) in
        assert (inner == FS.insert key (bucket_keys tl));
        // lhs = insert key (insert hd.ekey (bucket_keys (fst (remove_from_bucket tl key))))
        // We need to show this equals insert key (insert hd.ekey (bucket_keys tl))
        bucket_keys_after_remove tl key;
        // bucket_keys (fst (remove_from_bucket tl key)) = FS.remove key (bucket_keys tl)
        let s = bucket_keys tl in
        // lhs = insert key (insert hd.ekey (remove key s))
        // rhs = insert key (insert hd.ekey s)
        // These are equal if: insert hd.ekey (remove key s) has same membership as insert hd.ekey s after we insert key
        // Actually: insert key (insert a (remove key s)) = insert key (insert a s) for any a
        // Because inserting key at the end adds key regardless of whether it was removed
        assert (forall (x:k). FS.mem x (FS.insert key (FS.insert hd.ekey (FS.remove key s))) <==>
                            x = key \/ x = hd.ekey \/ (FS.mem x s /\ x <> key));
        assert (forall (x:k). FS.mem x (FS.insert key (FS.insert hd.ekey s)) <==>
                            x = key \/ x = hd.ekey \/ FS.mem x s);
        // These are equal because x = key covers the "x <> key" difference
        assert (forall (x:k). (x = key \/ x = hd.ekey \/ (FS.mem x s /\ x <> key)) <==>
                            (x = key \/ x = hd.ekey \/ FS.mem x s));
        assert (FS.equal lhs rhs)
      end

(** Union with emptyset on the left *)
let union_emptyset_left (#a:eqtype) (s:FS.set a)
  : Lemma (FS.union FS.emptyset s == s)
  = FS.all_finite_set_facts_lemma ();
    assert (forall (x:a). FS.mem x (FS.union FS.emptyset s) <==> FS.mem x FS.emptyset \/ FS.mem x s);
    assert (forall (x:a). FS.mem x (FS.union FS.emptyset s) <==> FS.mem x s);
    assert (FS.equal (FS.union FS.emptyset s) s)

(** Union with emptyset on the right *)
let union_emptyset_right (#a:eqtype) (s:FS.set a)
  : Lemma (FS.union s FS.emptyset == s)
  = FS.all_finite_set_facts_lemma ();
    assert (forall (x:a). FS.mem x (FS.union s FS.emptyset) <==> FS.mem x s \/ FS.mem x FS.emptyset);
    assert (forall (x:a). FS.mem x (FS.union s FS.emptyset) <==> FS.mem x s);
    assert (FS.equal (FS.union s FS.emptyset) s)

(** build_keys_from_buckets after update at one index - when past update_idx, they're equal *)
let rec build_keys_after_update_past (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (new_entries:list (entry k v))
  (idx:nat)
  : Lemma
    (requires idx > update_idx)
    (ensures (
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      build_keys_from_buckets new_contents idx == build_keys_from_buckets bucket_contents idx
    ))
    (decreases (Seq.length bucket_contents - idx))
  = FS.all_finite_set_facts_lemma ();
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= Seq.length bucket_contents then ()
    else begin
      build_keys_after_update_past bucket_contents update_idx new_entries (idx + 1);
      // At idx: Seq.index new_contents idx == Seq.index bucket_contents idx (since idx > update_idx)
      // So bucket_keys at idx are the same
      // By IH, the rest is the same too
      ()
    end

(** Key set after cons on one bucket - relates to insert on full key set *)
let rec build_keys_after_cons (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (new_entry:entry k v)
  (idx:nat)
  : Lemma
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let new_entries = new_entry :: old_entries in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      build_keys_from_buckets new_contents idx ==
      (if idx <= update_idx 
       then FS.insert new_entry.ekey (build_keys_from_buckets bucket_contents idx)
       else build_keys_from_buckets bucket_contents idx)
    ))
    (decreases (Seq.length bucket_contents - idx))
  = FS.all_finite_set_facts_lemma ();
    let old_entries = Seq.index bucket_contents update_idx in
    let new_entries = new_entry :: old_entries in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= Seq.length bucket_contents then ()
    else if idx = update_idx then begin
      build_keys_after_cons bucket_contents update_idx new_entry (idx + 1);
      // At update_idx: bucket_keys changes from old_entries to new_entries
      // bucket_keys new_entries = insert new_entry.ekey (bucket_keys old_entries)
      // new_keys at idx = union (bucket_keys new_entries) (build_keys rest)
      //                 = union (insert key (bucket_keys old_entries)) (build_keys rest)
      // old_keys at idx = union (bucket_keys old_entries) (build_keys rest)
      // Need: union (insert k s1) s2 = insert k (union s1 s2)
      let s1 = bucket_keys old_entries in
      let s2 = build_keys_from_buckets bucket_contents (idx + 1) in
      let lhs = FS.union (FS.insert new_entry.ekey s1) s2 in
      let rhs = FS.insert new_entry.ekey (FS.union s1 s2) in
      assert (forall (x:k). FS.mem x lhs <==> (x = new_entry.ekey \/ FS.mem x s1) \/ FS.mem x s2);
      assert (forall (x:k). FS.mem x rhs <==> x = new_entry.ekey \/ FS.mem x s1 \/ FS.mem x s2);
      assert (FS.equal lhs rhs)
    end else if idx < update_idx then begin
      build_keys_after_cons bucket_contents update_idx new_entry (idx + 1);
      // Before update_idx: this bucket unchanged, but recursive part adds key
      // new_keys at idx = union (bucket_keys (index new_contents idx)) (build_keys new_contents (idx+1))
      //                 = union (bucket_keys (index bucket_contents idx)) (insert key (build_keys bucket_contents (idx+1)))
      // old_keys at idx = union (bucket_keys (index bucket_contents idx)) (build_keys bucket_contents (idx+1))
      // Need: union s1 (insert k s2) = insert k (union s1 s2)
      let s1 = bucket_keys (Seq.index bucket_contents idx) in
      let s2 = build_keys_from_buckets bucket_contents (idx + 1) in
      let lhs = FS.union s1 (FS.insert new_entry.ekey s2) in
      let rhs = FS.insert new_entry.ekey (FS.union s1 s2) in
      assert (forall (x:k). FS.mem x lhs <==> FS.mem x s1 \/ (x = new_entry.ekey \/ FS.mem x s2));
      assert (forall (x:k). FS.mem x rhs <==> x = new_entry.ekey \/ FS.mem x s1 \/ FS.mem x s2);
      assert (FS.equal lhs rhs)
    end else begin
      // idx > update_idx: unchanged
      build_keys_after_cons bucket_contents update_idx new_entry (idx + 1)
    end

(** Key not in remaining buckets implies not in build_keys_from_buckets *)
let rec key_not_in_remaining_buckets (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (key:k)
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (idx:nat)
  : Lemma
    (requires 
      (forall (j:nat). j < Seq.length bucket_contents /\ j <> update_idx ==> 
        ~(key_in_bucket (Seq.index bucket_contents j) key)))
    (ensures ~(FS.mem key (build_keys_from_buckets bucket_contents idx)) \/ idx <= update_idx)
    (decreases (Seq.length bucket_contents - idx))
  = FS.all_finite_set_facts_lemma ();
    if idx >= Seq.length bucket_contents then ()
    else if idx = update_idx then ()
    else if idx > update_idx then begin
      key_not_in_remaining_buckets bucket_contents key update_idx (idx + 1);
      key_not_in_bucket_implies_not_in_keys (Seq.index bucket_contents idx) key
    end else 
      key_not_in_remaining_buckets bucket_contents key update_idx (idx + 1)

(** Helper: remove_from_bucket on absent key is no-op *)
let rec remove_absent_unchanged (#k:eqtype) (#v:Type0)
  (entries:list (entry k v)) (key:k)
  : Lemma
    (requires ~(key_in_bucket entries key))
    (ensures fst (remove_from_bucket entries key) == entries)
    (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl ->
      if hd.ekey = key then ()  // Contradiction with precondition
      else remove_absent_unchanged tl key

(** Seq.upd with same value is identity *)
let seq_upd_same (#a:Type) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Lemma (Seq.upd s i (Seq.index s i) == s)
  = Seq.lemma_eq_intro (Seq.upd s i (Seq.index s i)) s

(** Key set after remove when key is not in the bucket (remove is a no-op) *)
let build_keys_after_remove_absent (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k)
  : Lemma
    (requires ~(key_in_bucket (Seq.index bucket_contents update_idx) key))
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let new_entries = fst (remove_from_bucket old_entries key) in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      // When key not present, remove doesn't change the bucket
      new_entries == old_entries
    ))
  = remove_absent_unchanged (Seq.index bucket_contents update_idx) key

(** FS.remove of non-member gives the same set *)
let fs_remove_nonmember (#a:eqtype) (x:a) (s:FS.set a)
  : Lemma
    (requires ~(FS.mem x s))
    (ensures FS.remove x s == s)
  = FS.all_finite_set_facts_lemma ();
    // From FS facts: equal s1 s2 <==> (forall o. mem o s1 <==> mem o s2)
    // And: equal s1 s2 ==> s1 == s2
    // So we need: forall o. FS.mem o (FS.remove x s) <==> FS.mem o s
    // FS.remove x s = FS.difference s (FS.singleton x)
    // FS.mem o (FS.difference s (FS.singleton x)) <==> FS.mem o s /\ ~(FS.mem o (FS.singleton x))
    // FS.mem o (FS.singleton x) <==> o = x
    // So: FS.mem o (FS.remove x s) <==> FS.mem o s /\ o <> x
    // When ~(FS.mem x s): if o = x then both sides false, if o <> x then FS.mem o s <==> FS.mem o s
    assert (forall (o:a). FS.mem o (FS.remove x s) <==> FS.mem o s);
    // From equal_fact: this implies FS.equal (FS.remove x s) s
    assert (FS.equal (FS.remove x s) s)
    // From equal_extensionality_fact: this implies FS.remove x s == s

(** Key set after remove on one bucket *)
let rec build_keys_after_remove (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k)
  (idx:nat)
  : Lemma
    (requires 
      // Key is in the bucket at update_idx 
      key_in_bucket (Seq.index bucket_contents update_idx) key /\
      // Key is not in any other bucket
      (forall (j:nat). j < Seq.length bucket_contents /\ j <> update_idx ==> 
        ~(key_in_bucket (Seq.index bucket_contents j) key)) /\
      // All buckets have no duplicate keys
      all_buckets_no_dup bucket_contents 0)
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let new_entries = fst (remove_from_bucket old_entries key) in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      build_keys_from_buckets new_contents idx ==
      (if idx <= update_idx 
       then FS.remove key (build_keys_from_buckets bucket_contents idx)
       else build_keys_from_buckets bucket_contents idx)
    ))
    (decreases (Seq.length bucket_contents - idx))
  = FS.all_finite_set_facts_lemma ();
    let old_entries = Seq.index bucket_contents update_idx in
    let new_entries = fst (remove_from_bucket old_entries key) in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= Seq.length bucket_contents then ()
    else if idx = update_idx then begin
      build_keys_after_remove bucket_contents update_idx key (idx + 1);
      // At update_idx: bucket_keys changes
      // Extract no_dup_keys for this bucket
      all_buckets_no_dup_at bucket_contents update_idx;
      bucket_keys_after_remove old_entries key;
      // bucket_keys new_entries = FS.remove key (bucket_keys old_entries)
      // new_keys at idx = union (remove key (bucket_keys old_entries)) (build_keys rest)
      // old_keys at idx = union (bucket_keys old_entries) (build_keys rest)
      // Need: union (remove key s1) s2 = remove key (union s1 s2) when key not in s2
      // Key is not in any bucket after update_idx
      let s1 = bucket_keys old_entries in
      let s2 = build_keys_from_buckets bucket_contents (idx + 1) in
      // Show key not in s2
      key_not_in_remaining_buckets bucket_contents key update_idx (idx + 1);
      let lhs = FS.union (FS.remove key s1) s2 in
      let rhs = FS.remove key (FS.union s1 s2) in
      assert (forall (x:k). FS.mem x lhs <==> (FS.mem x s1 /\ x <> key) \/ FS.mem x s2);
      assert (forall (x:k). FS.mem x rhs <==> (FS.mem x s1 \/ FS.mem x s2) /\ x <> key);
      // Since key not in s2: these are equal
      assert (forall (x:k). FS.mem x s2 ==> x <> key);
      assert (forall (x:k). FS.mem x lhs <==> FS.mem x rhs);
      assert (FS.equal lhs rhs)
    end else if idx < update_idx then begin
      build_keys_after_remove bucket_contents update_idx key (idx + 1);
      // Before update_idx: this bucket unchanged, recursive part removes key
      // key not in this bucket
      assert (~(key_in_bucket (Seq.index bucket_contents idx) key));
      let s1 = bucket_keys (Seq.index bucket_contents idx) in
      let s2 = build_keys_from_buckets bucket_contents (idx + 1) in
      // Show key not in s1
      key_not_in_bucket_implies_not_in_keys (Seq.index bucket_contents idx) key;
      let lhs = FS.union s1 (FS.remove key s2) in
      let rhs = FS.remove key (FS.union s1 s2) in
      assert (forall (x:k). FS.mem x lhs <==> FS.mem x s1 \/ (FS.mem x s2 /\ x <> key));
      assert (forall (x:k). FS.mem x rhs <==> (FS.mem x s1 \/ FS.mem x s2) /\ x <> key);
      // Since key not in s1: these are equal
      assert (forall (x:k). FS.mem x s1 ==> x <> key);
      assert (forall (x:k). FS.mem x lhs <==> FS.mem x rhs);
      assert (FS.equal lhs rhs)
    end else begin
      // idx > update_idx: unchanged
      build_keys_after_remove bucket_contents update_idx key (idx + 1)
    end

(** Convenience wrapper for build_keys_after_remove that takes the new_contents directly *)
let build_keys_after_remove_explicit (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (new_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k)
  (keys:FS.set k)
  : Lemma
    (requires 
      // Key is in the bucket at update_idx 
      key_in_bucket (Seq.index bucket_contents update_idx) key /\
      // Key is not in any other bucket
      (forall (j:nat). j < Seq.length bucket_contents /\ j <> update_idx ==> 
        ~(key_in_bucket (Seq.index bucket_contents j) key)) /\
      // All buckets have no duplicate keys
      all_buckets_no_dup bucket_contents 0 /\
      // keys is what we think it is
      keys == build_keys_from_buckets bucket_contents 0 /\
      // new_contents is what the lemma expects
      new_contents == Seq.upd bucket_contents update_idx (fst (remove_from_bucket (Seq.index bucket_contents update_idx) key)))
    (ensures
      build_keys_from_buckets new_contents 0 == FS.remove key keys)
  = build_keys_after_remove bucket_contents update_idx key 0

(** Key in bucket implies key in bucket_keys *)
let rec key_in_bucket_implies_in_keys (#k:eqtype) (#v:Type0)
  (entries:list (entry k v)) (key:k)
  : Lemma
    (requires key_in_bucket entries key)
    (ensures FS.mem key (bucket_keys entries))
    (decreases entries)
  = FS.all_finite_set_facts_lemma ();
    match entries with
    | [] -> ()
    | hd::tl -> 
      if hd.ekey = key then ()
      else key_in_bucket_implies_in_keys tl key

(** Key in bucket at target_idx implies key in build_keys *)
let rec key_in_bucket_at_implies_key_in_build_keys (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (target_idx:nat{target_idx < Seq.length bucket_contents})
  (key:k)
  (idx:nat)
  : Lemma
    (requires 
      FS.mem key (bucket_keys (Seq.index bucket_contents target_idx)) /\
      idx <= target_idx)
    (ensures FS.mem key (build_keys_from_buckets bucket_contents idx))
    (decreases target_idx - idx)
  = FS.all_finite_set_facts_lemma ();
    if idx = target_idx then begin
      // At target_idx: build_keys = union (bucket_keys at idx) rest
      // FS.mem key (bucket_keys at idx), so FS.mem key (union ...)
      ()
    end else begin
      // Before target_idx: recurse
      key_in_bucket_at_implies_key_in_build_keys bucket_contents target_idx key (idx + 1)
      // By IH: FS.mem key (build_keys (idx+1))
      // build_keys idx = union (bucket_keys idx) (build_keys (idx+1))
      // So FS.mem key (build_keys idx)
    end

(** If key is in a bucket at idx, it's in build_keys_from_buckets *)
let key_in_bucket_implies_key_in_keys (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (hashf:k -> SZ.t)
  (capacity:pos{capacity == Seq.length bucket_contents})
  (idx:nat{idx < capacity})
  (key:k)
  : Lemma
    (requires 
      key_in_bucket (Seq.index bucket_contents idx) key /\
      all_buckets_wf bucket_contents hashf capacity 0)
    (ensures FS.mem key (build_keys_from_buckets bucket_contents 0))
  = FS.all_finite_set_facts_lemma ();
    key_in_bucket_implies_in_keys (Seq.index bucket_contents idx) key;
    // Now we have: FS.mem key (bucket_keys (Seq.index bucket_contents idx))
    // Need: FS.mem key (build_keys_from_buckets bucket_contents 0)
    // build_keys_from_buckets unions all bucket_keys
    key_in_bucket_at_implies_key_in_build_keys bucket_contents idx key 0

(** Helper: if key hashes to hash_idx but bucket at idx has wf with idx <> hash_idx, key not in that bucket *)
let rec key_in_wrong_bucket_aux (#k:eqtype) (#v:Type0)
  (entries:list (entry k v))
  (hashf:k -> SZ.t)
  (capacity:pos)
  (idx:nat{idx < capacity})
  (hash_idx:nat{hash_idx < capacity})
  (key:k)
  : Lemma
    (requires 
      bucket_wf entries hashf capacity idx /\
      hash_idx <> idx /\
      SZ.v (hashf key) % capacity == hash_idx)
    (ensures ~(key_in_bucket entries key))
    (decreases entries)
  = match entries with
    | [] -> ()
    | hd::tl -> 
      // hd.ekey hashes to idx (by wf), but key hashes to hash_idx <> idx
      // So hd.ekey <> key
      key_in_wrong_bucket_aux tl hashf capacity idx hash_idx key

let key_in_wrong_bucket_means_not_in (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (hashf:k -> SZ.t)
  (capacity:pos{capacity == Seq.length bucket_contents})
  (idx:nat{idx < capacity})
  (hash_idx:nat{hash_idx < capacity})
  (key:k)
  : Lemma
    (requires 
      bucket_wf (Seq.index bucket_contents idx) hashf capacity idx /\
      hash_idx <> idx /\
      SZ.v (hashf key) % capacity == hash_idx)
    (ensures ~(key_in_bucket (Seq.index bucket_contents idx) key))
  = key_in_wrong_bucket_aux (Seq.index bucket_contents idx) hashf capacity idx hash_idx key

(** If key is NOT in the bucket at the hash index, it's not in any bucket (by well-formedness) *)
let rec key_not_in_hash_bucket_implies_not_in_any (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (hashf:k -> SZ.t)
  (capacity:pos{capacity == Seq.length bucket_contents})
  (key:k)
  (idx:nat)
  : Lemma
    (requires 
      all_buckets_wf bucket_contents hashf capacity 0 /\
      ~(key_in_bucket (Seq.index bucket_contents (SZ.v (hashf key) % capacity)) key))
    (ensures ~(FS.mem key (build_keys_from_buckets bucket_contents idx)))
    (decreases (capacity - idx))
  = FS.all_finite_set_facts_lemma ();
    if idx >= capacity then ()
    else begin
      key_not_in_hash_bucket_implies_not_in_any bucket_contents hashf capacity key (idx + 1);
      // Need: ~(FS.mem key (bucket_keys (Seq.index bucket_contents idx)))
      // Case 1: idx == hash_idx: already know ~(key_in_bucket ...)
      // Case 2: idx <> hash_idx: by wf, key doesn't hash here, so not in this bucket
      let hash_idx = SZ.v (hashf key) % capacity in
      if idx = hash_idx then
        key_not_in_bucket_implies_not_in_keys (Seq.index bucket_contents idx) key
      else begin
        // key not in bucket at idx because it would hash to hash_idx, not idx
        // by bucket_wf, all keys in bucket at idx hash to idx
        all_buckets_wf_at bucket_contents hashf capacity idx;
        key_in_wrong_bucket_means_not_in bucket_contents hashf capacity idx hash_idx key;
        key_not_in_bucket_implies_not_in_keys (Seq.index bucket_contents idx) key
      end
    end

(** If key is in bucket at hash_idx, it's not in any other bucket (by wf) *)
let key_only_in_hash_bucket (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (hashf:k -> SZ.t)
  (capacity:pos{capacity == Seq.length bucket_contents})
  (hash_idx:nat{hash_idx < capacity})
  (key:k)
  : Lemma
    (requires 
      all_buckets_wf bucket_contents hashf capacity 0 /\
      key_in_bucket (Seq.index bucket_contents hash_idx) key /\
      hash_idx == SZ.v (hashf key) % capacity)
    (ensures 
      forall (j:nat). j < capacity /\ j <> hash_idx ==> ~(key_in_bucket (Seq.index bucket_contents j) key))
  = let aux (j:nat{j < capacity /\ j <> hash_idx})
      : Lemma (~(key_in_bucket (Seq.index bucket_contents j) key))
      = all_buckets_wf_at bucket_contents hashf capacity j;
        key_in_wrong_bucket_means_not_in bucket_contents hashf capacity j hash_idx key
    in
    FStar.Classical.forall_intro aux

(** Cons after remove for direct build_keys computation *)
let rec build_keys_cons_remove_direct (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k) (value:v)
  (idx:nat)
  : Lemma
    (requires all_buckets_no_dup bucket_contents 0)
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let removed_entries = fst (remove_from_bucket old_entries key) in
      let new_entries = {ekey=key; evalue=value} :: removed_entries in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      build_keys_from_buckets new_contents idx ==
      (if idx <= update_idx 
       then FS.insert key (build_keys_from_buckets bucket_contents idx)
       else build_keys_from_buckets bucket_contents idx)
    ))
    (decreases (Seq.length bucket_contents - idx))
  = FS.all_finite_set_facts_lemma ();
    let old_entries = Seq.index bucket_contents update_idx in
    let removed_entries = fst (remove_from_bucket old_entries key) in
    let new_entries : list (entry k v) = {ekey=key; evalue=value} :: removed_entries in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    if idx >= Seq.length bucket_contents then ()
    else if idx = update_idx then begin
      build_keys_cons_remove_direct bucket_contents update_idx key value (idx + 1);
      all_buckets_no_dup_at bucket_contents update_idx;
      bucket_keys_cons_after_remove old_entries key value;
      // bucket_keys new_entries = insert key (bucket_keys old_entries)
      let s1_new = bucket_keys new_entries in
      let s1_old = bucket_keys old_entries in
      let s2 = build_keys_from_buckets bucket_contents (idx + 1) in
      // new_keys = union s1_new s2 = union (insert key s1_old) s2
      // old_keys = union s1_old s2
      // Need: union (insert key s1) s2 = insert key (union s1 s2)
      let lhs = FS.union (FS.insert key s1_old) s2 in
      let rhs = FS.insert key (FS.union s1_old s2) in
      assert (forall (x:k). FS.mem x lhs <==> (x = key \/ FS.mem x s1_old) \/ FS.mem x s2);
      assert (forall (x:k). FS.mem x rhs <==> x = key \/ FS.mem x s1_old \/ FS.mem x s2);
      assert (FS.equal lhs rhs)
    end else if idx < update_idx then begin
      build_keys_cons_remove_direct bucket_contents update_idx key value (idx + 1);
      let s1 = bucket_keys (Seq.index bucket_contents idx) in
      let s2_new = build_keys_from_buckets new_contents (idx + 1) in
      let s2_old = build_keys_from_buckets bucket_contents (idx + 1) in
      // By IH: s2_new = insert key s2_old
      // new_keys = union s1 s2_new = union s1 (insert key s2_old)
      // old_keys = union s1 s2_old
      // Need: union s1 (insert key s2) = insert key (union s1 s2)
      let lhs = FS.union s1 (FS.insert key s2_old) in
      let rhs = FS.insert key (FS.union s1 s2_old) in
      assert (forall (x:k). FS.mem x lhs <==> FS.mem x s1 \/ (x = key \/ FS.mem x s2_old));
      assert (forall (x:k). FS.mem x rhs <==> x = key \/ FS.mem x s1 \/ FS.mem x s2_old);
      assert (FS.equal lhs rhs)
    end else begin
      build_keys_cons_remove_direct bucket_contents update_idx key value (idx + 1)
    end

(** Cons after remove preserves key set for full build_keys *)
let build_keys_after_cons_remove (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (update_idx:nat{update_idx < Seq.length bucket_contents})
  (key:k) (value:v)
  : Lemma
    (requires 
      all_buckets_no_dup bucket_contents 0 /\
      all_buckets_wf bucket_contents (fun _ -> 0sz) (Seq.length bucket_contents) 0)  // dummy hashf, not used
    (ensures (
      let old_entries = Seq.index bucket_contents update_idx in
      let removed_entries = fst (remove_from_bucket old_entries key) in
      let new_entries = {ekey=key; evalue=value} :: removed_entries in
      let new_contents = Seq.upd bucket_contents update_idx new_entries in
      build_keys_from_buckets new_contents 0 ==
      FS.insert key (build_keys_from_buckets bucket_contents 0)
    ))
  = let old_entries = Seq.index bucket_contents update_idx in
    let removed_entries = fst (remove_from_bucket old_entries key) in
    let new_entries = {ekey=key; evalue=value} :: removed_entries in
    let new_contents = Seq.upd bucket_contents update_idx new_entries in
    // This follows from build_keys_after_cons applied to the intermediate state
    // First update: Seq.upd to get removed_entries
    // Second update: cons new_entry
    // For simplicity, we'll prove directly using membership
    FS.all_finite_set_facts_lemma ();
    // Extract no_dup for this bucket
    all_buckets_no_dup_at bucket_contents update_idx;
    bucket_keys_cons_after_remove old_entries key value;
    // bucket_keys new_entries = FS.insert key (bucket_keys old_entries)
    // Now need to show build_keys with new_contents = insert key (build_keys with bucket_contents)
    build_keys_after_cons bucket_contents update_idx {ekey=key; evalue=value} 0;
    // But wait, we're not just consing - we're doing cons after remove
    // Let me think more carefully...
    // new_entries = {key, value} :: fst(remove old_entries key)
    // bucket_keys new_entries = insert key (bucket_keys (fst(remove old_entries key)))
    //                        = insert key (remove key (bucket_keys old_entries)) [by bucket_keys_after_remove]
    // If no_dup_keys old_entries, then insert key (remove key (bucket_keys old_entries)) = bucket_keys old_entries... no wait
    // Actually: insert key (remove key s) = insert key s  (because insert adds key regardless)
    // So bucket_keys new_entries = insert key (bucket_keys old_entries)
    // Now we can use build_keys_after_cons but with the intermediate seq
    // Actually let's prove this directly:
    build_keys_cons_remove_direct bucket_contents update_idx key value 0

(** Connect seq_index_opt to Seq.index for all-empty case *)
let seq_index_opt_to_index (#a:Type) (s:Seq.seq a) (cap:nat) (v:a)
  : Lemma 
    (requires Seq.length s == cap /\ (forall (j:nat). j < cap ==> seq_index_opt s j == Some v))
    (ensures forall (j:nat). j < cap ==> Seq.index s j == v)
  = ()

(** Initialize buckets recursively from index i up to capacity *)
fn rec init_buckets
  (#k:eqtype)
  (#v:Type0)
  (buckets:V.vec (bucket k v))
  (capacity:SZ.t{SZ.v capacity > 0})
  (i:SZ.t)
  (#bucket_ptrs:erased (Seq.seq (bucket k v)))
requires
  V.pts_to buckets bucket_ptrs **
  pure (Seq.length bucket_ptrs == SZ.v capacity /\ SZ.v i <= SZ.v capacity)
ensures exists* (new_ptrs:Seq.seq (bucket k v)) (new_contents:Seq.seq (list (entry k v))).
  V.pts_to buckets new_ptrs **
  OR.on_range (bucket_at new_ptrs new_contents) (SZ.v i) (SZ.v capacity) **
  pure (
    Seq.length new_ptrs == SZ.v capacity /\
    Seq.length new_contents == SZ.v capacity /\
    (forall (j:nat). j < SZ.v i ==> seq_index_opt new_ptrs j == seq_index_opt bucket_ptrs j) /\
    (forall (j:nat). SZ.v i <= j /\ j < SZ.v capacity ==> seq_index_opt new_contents j == Some [])
  )
decreases (SZ.v capacity - SZ.v i)
{
  if (i = capacity) {
    // Base case: i = capacity, on_range from capacity to capacity is empty
    let new_contents : erased (Seq.seq (list (entry k v))) = Seq.create (SZ.v capacity) [];
    assert (pure (Seq.length new_contents == SZ.v capacity));
    OR.on_range_empty (bucket_at bucket_ptrs new_contents) (SZ.v capacity);
    ()
  } else {
    // Recursive case: first initialize bucket i, then recurse on i+1
    
    // Create a fresh empty list for slot i
    let empty_list = LL.create (entry k v);
    
    // Write the empty list pointer to slot i using Vec's op_Array_Assignment
    V.op_Array_Assignment buckets i empty_list;
    with s'. _;
    
    // s' == Seq.upd bucket_ptrs (SZ.v i) empty_list
    let i_plus_1 = SZ.add i 1sz;
    
    // Recurse to initialize [i+1, capacity)
    init_buckets buckets capacity i_plus_1;
    with new_ptrs new_contents. _;
    
    // Now we have:
    //   pts_to buckets new_ptrs
    //   on_range [i+1, capacity)
    //   is_list empty_list []
    
    // We need to combine is_list empty_list [] with on_range [i+1, cap)
    // to get on_range [i, cap)
    
    // First, create bucket_at for index i
    let final_contents : erased (Seq.seq (list (entry k v))) = Seq.upd new_contents (SZ.v i) [];
    
    assert (pure (Seq.index new_ptrs (SZ.v i) == empty_list));
    assert (pure (Seq.index final_contents (SZ.v i) == []));
    
    rewrite (LL.is_list empty_list [])
         as (LL.is_list (Seq.index new_ptrs (SZ.v i)) (Seq.index final_contents (SZ.v i)));
    rewrite (LL.is_list (Seq.index new_ptrs (SZ.v i)) (Seq.index final_contents (SZ.v i)))
         as (bucket_at new_ptrs final_contents (SZ.v i));
    
    // Need to rewrite on_range to use final_contents instead of new_contents
    // For j >= i+1: final_contents[j] == new_contents[j] (Seq.upd only changes i)
    // Provide a function that shows each bucket_at is unchanged
    ghost
    fn weaken_bucket (k:nat{SZ.v i_plus_1 <= k /\ k < SZ.v capacity})
      requires bucket_at new_ptrs new_contents k
      ensures bucket_at new_ptrs final_contents k
    {
      // For k > i: Seq.index final_contents k == Seq.index new_contents k
      // because Seq.upd only changed index i, and k > i
      assert (pure (Seq.index final_contents k == Seq.index new_contents k));
      rewrite (bucket_at new_ptrs new_contents k)
           as (bucket_at new_ptrs final_contents k)
    };
    
    OR.on_range_weaken 
      (bucket_at new_ptrs new_contents)
      (bucket_at new_ptrs final_contents)
      (SZ.v i_plus_1) (SZ.v capacity)
      weaken_bucket;
    
    // Combine: bucket_at at i + on_range [i+1, cap) = on_range [i, cap)
    OR.on_range_cons (SZ.v i);
    
    ()
  }
}

fn create
  (#k:eqtype)
  (#v:Type0)
  (hashf:(k -> SZ.t))
  (initial_capacity:SZ.t{SZ.v initial_capacity > 0})
requires emp
returns h:ht k v
ensures is_ht h empty_pmap FS.emptyset
{
  // Create a dummy bucket (will be overwritten)
  let dummy = LL.create (entry k v);
  
  // Allocate vector of buckets
  let buckets = V.alloc dummy initial_capacity;
  
  // Allocate count using Box (heap-allocated and freeable)
  let count = B.alloc 0sz;
  
  // Initialize all buckets with fresh empty lists (from 0 to capacity)
  init_buckets buckets initial_capacity 0sz;
  with final_ptrs final_contents. _;
  
  // Build the hash table
  let h : ht k v = {
    buckets = buckets;
    count = count;
    capacity = initial_capacity;
    hashf = hashf;
  };
  
  // Prove the invariants
  // First, establish that all buckets are empty using seq_index_opt_to_index
  seq_index_opt_to_index final_contents (SZ.v initial_capacity) ([] #(entry k v));
  
  all_empty_buckets_wf #k #v final_contents hashf (SZ.v initial_capacity) 0;
  empty_buckets_zero_count #k #v final_contents 0;
  empty_buckets_equal_empty_pmap #k #v final_contents hashf (SZ.v initial_capacity);
  empty_buckets_no_dup #k #v final_contents 0;
  empty_buckets_keys #k #v final_contents 0;
  empty_keys_cardinality #k #v final_contents 0;
  
  // The dummy bucket is null_llist, so is_list dummy [] is just pure (dummy == None)
  // This is emp modulo the pure fact, so we can safely drop it
  // (This doesn't leak memory - empty lists are null pointers)
  drop_ (LL.is_list dummy []);
  
  // Rewrite resources to use h's fields
  rewrite (V.pts_to buckets final_ptrs) as (V.pts_to h.buckets final_ptrs);
  rewrite (B.pts_to count 0sz) as (B.pts_to h.count 0sz);
  
  fold (is_ht h empty_pmap FS.emptyset);
  h
}

//////////////////////////////////////////////////////////////////////////////
// Lookup
//////////////////////////////////////////////////////////////////////////////

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
{
  unfold (is_ht h m keys);
  with bucket_ptrs bucket_contents cnt. _;
  
  // Compute bucket index
  let hash_val = h.hashf key;
  let idx = SZ.rem hash_val h.capacity;
  let idx_nat = SZ.v idx;
  
  // Get the bucket with trade to restore
  get_bucket_at bucket_ptrs bucket_contents 0 (SZ.v h.capacity) idx_nat;
  unfold_bucket_at bucket_ptrs bucket_contents idx_nat;
  
  // Get the actual bucket pointer from the vector
  let b = V.op_Array_Access h.buckets idx;
  
  // The bucket from vector should equal the one from sequence
  // rewrite to use b
  rewrite (LL.is_list (Seq.index bucket_ptrs idx_nat) (Seq.index bucket_contents idx_nat))
       as (LL.is_list b (Seq.index bucket_contents idx_nat));
  
  // Search in the bucket
  let result = search_bucket_rec b key;
  
  // Rewrite back
  rewrite (LL.is_list b (Seq.index bucket_contents idx_nat))
       as (LL.is_list (Seq.index bucket_ptrs idx_nat) (Seq.index bucket_contents idx_nat));
  
  // Restore bucket_at
  fold_bucket_at bucket_ptrs bucket_contents idx_nat;
  
  // Put bucket back into on_range
  put_bucket_at bucket_ptrs bucket_contents 0 (SZ.v h.capacity) idx_nat;
  
  // Use the lookup_correct lemma to prove result == m key
  lookup_correct bucket_contents h.hashf (SZ.v h.capacity) key;
  
  fold (is_ht h m keys);
  result
}

//////////////////////////////////////////////////////////////////////////////
// Insert
//////////////////////////////////////////////////////////////////////////////

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
{
  unfold (is_ht h m keys);
  with bucket_ptrs bucket_contents cnt. _;
  
  // Compute bucket index
  let hash = h.hashf key;
  let idx = SZ.rem hash h.capacity;
  let idx_nat : nat = SZ.v idx;
  
  // Read the bucket pointer from the vector (concrete value)
  let b = V.op_Array_Access h.buckets idx;
  
  // Split on_range at idx using on_range_get
  OR.on_range_get idx_nat;
  
  // Now we have:
  //   on_range [0, idx) ** bucket_at idx ** on_range [idx+1, capacity)
  
  // bucket_at gives us is_list for this bucket
  unfold_bucket_at bucket_ptrs bucket_contents idx_nat;
  
  // Rewrite to use b (the concrete pointer we read)
  rewrite (LL.is_list (Seq.index bucket_ptrs idx_nat) (Seq.index bucket_contents idx_nat))
       as (LL.is_list b (Seq.index bucket_contents idx_nat));
  
  // First remove existing entry with this key (if any)
  let (removed_b, was_removed) = remove_from_bucket_fn b key;
  
  // Now cons new entry to front
  let new_entry : entry k v = { ekey = key; evalue = value };
  let new_b = LL.cons new_entry removed_b;
  
  // Compute new bucket contents: cons onto removed entries
  let old_entries : Ghost.erased (list (entry k v)) = Seq.index bucket_contents idx_nat;
  let removed_entries : Ghost.erased (list (entry k v)) = fst (remove_from_bucket old_entries key);
  let new_entries : Ghost.erased (list (entry k v)) = new_entry :: removed_entries;
  
  // Write the new bucket pointer back to the vector
  V.op_Array_Assignment h.buckets idx new_b;
  with new_bucket_ptrs. _;
  
  // new_bucket_ptrs == Seq.upd bucket_ptrs idx_nat new_b
  
  // Create new bucket_contents with updated bucket
  let new_bucket_contents : Ghost.erased (Seq.seq (list (entry k v))) = Seq.upd bucket_contents idx_nat new_entries;
  
  // Rewrite is_list to match new sequences
  rewrite (LL.is_list new_b new_entries)
       as (LL.is_list (Seq.index new_bucket_ptrs idx_nat) (Seq.index new_bucket_contents idx_nat));
  
  // Fold back to bucket_at with new sequences
  fold_bucket_at new_bucket_ptrs new_bucket_contents idx_nat;
  
  // Now we need to weaken the on_range parts to use new_bucket_ptrs/new_bucket_contents
  // For indices < idx: new_bucket_ptrs[j] == bucket_ptrs[j] and new_bucket_contents[j] == bucket_contents[j]
  // For indices > idx: similarly unchanged
  
  ghost
  fn weaken_lo (j:nat{0 <= j /\ j < idx_nat})
    requires bucket_at bucket_ptrs bucket_contents j
    ensures bucket_at new_bucket_ptrs new_bucket_contents j
  {
    // j < idx, so Seq.upd doesn't change index j
    rewrite (bucket_at bucket_ptrs bucket_contents j)
         as (bucket_at new_bucket_ptrs new_bucket_contents j)
  };
  
  ghost
  fn weaken_hi (j:nat{idx_nat + 1 <= j /\ j < SZ.v h.capacity})
    requires bucket_at bucket_ptrs bucket_contents j
    ensures bucket_at new_bucket_ptrs new_bucket_contents j
  {
    // j > idx, so Seq.upd doesn't change index j
    rewrite (bucket_at bucket_ptrs bucket_contents j)
         as (bucket_at new_bucket_ptrs new_bucket_contents j)
  };
  
  OR.on_range_weaken
    (bucket_at bucket_ptrs bucket_contents)
    (bucket_at new_bucket_ptrs new_bucket_contents)
    0 idx_nat
    weaken_lo;
  
  OR.on_range_weaken
    (bucket_at bucket_ptrs bucket_contents)
    (bucket_at new_bucket_ptrs new_bucket_contents)
    (idx_nat + 1) (SZ.v h.capacity)
    weaken_hi;
  
  // Now combine the three parts back into one on_range
  OR.on_range_put 0 idx_nat (SZ.v h.capacity);
  
  // Now we have on_range [0, capacity) with new_bucket_ptrs/new_bucket_contents
  
  // Prove the properties needed for fold (these don't depend on count)
  
  // 1. Spec equality: remove then cons = insert
  remove_cons_insert_pmap_correct_full bucket_contents h.hashf (SZ.v h.capacity) key value;
  
  // 2. Count: total_count new_bucket_contents 0 depends on was_removed
  total_count_remove_cons_full bucket_contents idx_nat key value;
  
  // 3. Well-formedness: all_buckets_wf new_bucket_contents h.hashf (SZ.v h.capacity) 0
  all_buckets_wf_remove_cons bucket_contents h.hashf (SZ.v h.capacity) idx_nat key value 0;
  
  // 4. No duplicate keys: all_buckets_no_dup new_bucket_contents 0
  all_buckets_no_dup_remove_cons bucket_contents idx_nat key value 0;
  
  // 5. Key set: build_keys_from_buckets new_bucket_contents 0 == FS.insert key (build_keys_from_buckets bucket_contents 0)
  build_keys_cons_remove_direct bucket_contents idx_nat key value 0;
  
  // 6. Cardinality lemmas
  // From invariant: keys == build_keys_from_buckets bucket_contents 0
  // From #5: build_keys_from_buckets new_bucket_contents 0 == FS.insert key keys
  // Need: FS.cardinality (FS.insert key keys) computation
  FS.all_finite_set_facts_lemma ();
  // If was_removed: key was in keys, so insert key keys == keys (no change to cardinality)
  // If not was_removed: key was not in keys, so cardinality increases by 1
  
  // was_removed == snd (remove_from_bucket old_entries key) == key_in_bucket old_entries key
  remove_returns_key_in_bucket (Seq.index bucket_contents idx_nat) key;
  // So: was_removed <==> key_in_bucket old_entries key
  
  // Update count based on whether we removed an existing entry
  // And fold the invariant in each branch
  if was_removed {
    // key_in_bucket is true, so we can prove key in keys
    key_in_bucket_implies_key_in_keys bucket_contents h.hashf (SZ.v h.capacity) idx_nat key;
    // FS.mem key keys, so FS.insert key keys has same cardinality
    // No change to count - just rewrote existing entry
    // total_count new_bucket_contents 0 == total_count bucket_contents 0 == cnt
    // key was in keys, so FS.insert key keys == keys (no cardinality change)
    // FS.cardinality (FS.insert key keys) == FS.cardinality keys == cnt
    fold (is_ht h (insert_pmap m key value) (FS.insert key keys))
  } else {
    // key_in_bucket is false at hash bucket, so key not in any bucket, so key not in keys
    key_not_in_hash_bucket_implies_not_in_any bucket_contents h.hashf (SZ.v h.capacity) key 0;
    // ~(FS.mem key keys), so FS.insert key keys increases cardinality by 1
    // New entry - increment count
    // total_count new_bucket_contents 0 == total_count bucket_contents 0 + 1 == cnt + 1
    // key was NOT in keys, so FS.cardinality (FS.insert key keys) == FS.cardinality keys + 1
    let old_cnt = B.op_Bang h.count;
    // From precondition: SZ.fits (FS.cardinality keys + 1)
    // From invariant: SZ.v cnt == FS.cardinality keys
    // So SZ.fits (SZ.v old_cnt + 1)
    let new_cnt : SZ.t = SZ.add old_cnt 1sz;
    B.op_Colon_Equals h.count new_cnt;
    fold (is_ht h (insert_pmap m key value) (FS.insert key keys))
  }
}

//////////////////////////////////////////////////////////////////////////////
// Remove
//////////////////////////////////////////////////////////////////////////////

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
{
  unfold (is_ht h m keys);
  with bucket_ptrs bucket_contents cnt. _;
  
  // Compute bucket index
  let hash = h.hashf key;
  let idx = SZ.rem hash h.capacity;
  let idx_nat : nat = SZ.v idx;
  
  // Read the bucket pointer from the vector (concrete value)
  let b = V.op_Array_Access h.buckets idx;
  
  // Split on_range at idx using on_range_get
  OR.on_range_get idx_nat;
  
  // bucket_at gives us is_list for this bucket
  unfold_bucket_at bucket_ptrs bucket_contents idx_nat;
  
  // Rewrite to use b (the concrete pointer we read)
  rewrite (LL.is_list (Seq.index bucket_ptrs idx_nat) (Seq.index bucket_contents idx_nat))
       as (LL.is_list b (Seq.index bucket_contents idx_nat));
  
  // Remove the entry from the bucket
  let (new_b, removed) = remove_from_bucket_fn b key;
  
  // Compute the new bucket contents
  let old_entries : Ghost.erased (list (entry k v)) = Seq.index bucket_contents idx_nat;
  let new_entries : Ghost.erased (list (entry k v)) = fst (remove_from_bucket old_entries key);
  
  // Write the new bucket pointer back to the vector
  V.op_Array_Assignment h.buckets idx new_b;
  with new_bucket_ptrs. _;
  
  // Create new bucket_contents with updated bucket
  let new_bucket_contents : Ghost.erased (Seq.seq (list (entry k v))) = Seq.upd bucket_contents idx_nat new_entries;
  
  // Rewrite is_list to match new sequences
  rewrite (LL.is_list new_b new_entries)
       as (LL.is_list (Seq.index new_bucket_ptrs idx_nat) (Seq.index new_bucket_contents idx_nat));
  
  // Fold back to bucket_at with new sequences
  fold_bucket_at new_bucket_ptrs new_bucket_contents idx_nat;
  
  // Weaken the on_range parts
  ghost
  fn weaken_lo (j:nat{0 <= j /\ j < idx_nat})
    requires bucket_at bucket_ptrs bucket_contents j
    ensures bucket_at new_bucket_ptrs new_bucket_contents j
  {
    rewrite (bucket_at bucket_ptrs bucket_contents j)
         as (bucket_at new_bucket_ptrs new_bucket_contents j)
  };
  
  ghost
  fn weaken_hi (j:nat{idx_nat + 1 <= j /\ j < SZ.v h.capacity})
    requires bucket_at bucket_ptrs bucket_contents j
    ensures bucket_at new_bucket_ptrs new_bucket_contents j
  {
    rewrite (bucket_at bucket_ptrs bucket_contents j)
         as (bucket_at new_bucket_ptrs new_bucket_contents j)
  };
  
  OR.on_range_weaken
    (bucket_at bucket_ptrs bucket_contents)
    (bucket_at new_bucket_ptrs new_bucket_contents)
    0 idx_nat
    weaken_lo;
  
  OR.on_range_weaken
    (bucket_at bucket_ptrs bucket_contents)
    (bucket_at new_bucket_ptrs new_bucket_contents)
    (idx_nat + 1) (SZ.v h.capacity)
    weaken_hi;
  
  // Combine back into one on_range
  OR.on_range_put 0 idx_nat (SZ.v h.capacity);
  
  // Prove the properties (independent of count)
  // Count: use total_count_remove lemma
  total_count_remove bucket_contents idx_nat key 0;
  
  // Well-formedness: use all_buckets_wf_remove lemma  
  all_buckets_wf_remove bucket_contents h.hashf (SZ.v h.capacity) idx_nat key 0;
  
  // No duplicate keys preserved
  all_buckets_no_dup_remove bucket_contents idx_nat key 0;
  
  // Spec equality: Now that we have all_buckets_no_dup in invariant, we can prove this!
  remove_bucket_correct_full bucket_contents h.hashf (SZ.v h.capacity) key;
  
  // Prove that removed == Some? (m key)
  remove_returns_some bucket_contents h.hashf (SZ.v h.capacity) key;
  // Now we have: snd (remove_from_bucket (Seq.index bucket_contents idx_nat) key) == Some? (m key)
  // And removed == snd (remove_from_bucket (Seq.index bucket_contents idx_nat) key) from postcondition of remove_from_bucket_fn
  // So removed == Some? (m key)
  assert (pure (removed == Some? (reveal m key)));
  
  // Key set and cardinality lemmas
  FS.all_finite_set_facts_lemma ();
  
  // removed == key_in_bucket (Seq.index bucket_contents idx_nat) key
  remove_returns_key_in_bucket (Seq.index bucket_contents idx_nat) key;
  
  // Establish idx_nat == SZ.v (h.hashf key) % SZ.v h.capacity
  // This follows from: idx = SZ.rem hash h.capacity, hash = h.hashf key, idx_nat = SZ.v idx
  // And SZ.v (SZ.rem a b) = SZ.v a % SZ.v b when SZ.v b > 0
  assert (pure (idx_nat == SZ.v (h.hashf key) % SZ.v h.capacity));
  
  // Update count and fold in each branch
  if removed {
    // Key was in the bucket at idx_nat
    // Bring FiniteSet facts into scope for SMT
    FS.all_finite_set_facts_lemma ();
    
    // removed == key_in_bucket (Seq.index bucket_contents idx_nat) key
    // So in this branch: key_in_bucket (Seq.index bucket_contents idx_nat) key
    
    // 1. Key is only in bucket at hash index (by wf)
    key_only_in_hash_bucket bucket_contents h.hashf (SZ.v h.capacity) idx_nat key;
    
    // 2. Establish that new_bucket_contents has the expected form
    // new_bucket_contents == Seq.upd bucket_contents idx_nat (fst (remove_from_bucket ...))
    // This is definitionally true from how new_bucket_contents was computed
    assert (pure (Ghost.reveal new_bucket_contents == update_bucket bucket_contents idx_nat (fst (remove_from_bucket (Seq.index bucket_contents idx_nat) key))));
    
    // 3. Use explicit lemma for pmap equality
    remove_bucket_correct_full_explicit bucket_contents (Ghost.reveal new_bucket_contents) h.hashf (SZ.v h.capacity) key m;
    // This directly proves: build_pmap_from_buckets new_bucket_contents 0 == remove_pmap m key
    
    // 4. Use build_keys_after_remove_explicit
    build_keys_after_remove_explicit bucket_contents (Ghost.reveal new_bucket_contents) idx_nat key keys;
    // This directly proves: build_keys_from_buckets new_bucket_contents 0 == FS.remove key keys
    
    // 5. Prove key in keys, so cardinality >= 1
    key_in_bucket_implies_key_in_keys bucket_contents h.hashf (SZ.v h.capacity) idx_nat key;
    assert (pure (FS.mem key keys));
    
    // 7. Total count after remove
    assert (pure (total_count (Ghost.reveal new_bucket_contents) 0 == total_count bucket_contents 0 - 1));
    
    // Count decreases by 1
    let old_cnt = B.op_Bang h.count;
    assert (pure (SZ.v old_cnt == FS.cardinality keys));
    assert (pure (SZ.v old_cnt >= 1));
    
    let new_cnt : SZ.t = SZ.sub old_cnt 1sz;
    assert (pure (SZ.v new_cnt == FS.cardinality keys - 1));
    assert (pure (SZ.v new_cnt == FS.cardinality (FS.remove key keys)));
    assert (pure (SZ.v new_cnt == total_count (Ghost.reveal new_bucket_contents) 0));
    
    B.op_Colon_Equals h.count new_cnt;
    fold (is_ht h (remove_pmap m key) (FS.remove key keys));
    true
  } else {
    // Key was NOT in the bucket at idx_nat
    // Bring FiniteSet facts into scope for SMT
    FS.all_finite_set_facts_lemma ();
    
    // Since key hashes to idx_nat, key is not in ANY bucket (by wf)
    build_keys_after_remove_absent bucket_contents idx_nat key;
    // This proves: fst (remove_from_bucket (Seq.index bucket_contents idx_nat) key) == Seq.index bucket_contents idx_nat
    // Since old_entries = Seq.index bucket_contents idx_nat and new_entries = fst (remove_from_bucket old_entries key),
    // we have new_entries == Seq.index bucket_contents idx_nat
    assert (pure (Ghost.reveal new_entries == Seq.index bucket_contents idx_nat));
    
    key_not_in_hash_bucket_implies_not_in_any bucket_contents h.hashf (SZ.v h.capacity) key 0;
    // This proves: ~(FS.mem key (build_keys_from_buckets bucket_contents 0))
    // Since keys == build_keys_from_buckets bucket_contents 0, we have ~(FS.mem key keys)
    assert (pure (~(FS.mem key keys)));
    
    // Since key not in keys: FS.remove key keys == keys
    fs_remove_nonmember key keys;
    assert (pure (FS.remove key keys == keys));
    
    // Since key not in any bucket: remove_pmap m key == m
    // (removing a key that doesn't exist doesn't change the map)
    remove_pmap_absent bucket_contents h.hashf (SZ.v h.capacity) key;
    assert (pure (remove_pmap m key == m));
    
    // new_bucket_contents = Seq.upd bucket_contents idx_nat new_entries
    //                     = Seq.upd bucket_contents idx_nat (Seq.index bucket_contents idx_nat)
    seq_upd_same bucket_contents idx_nat;
    // This proves: Seq.upd bucket_contents idx_nat (Seq.index bucket_contents idx_nat) == bucket_contents
    assert (pure (Ghost.reveal new_bucket_contents == bucket_contents));
    
    // With new_bucket_contents == bucket_contents, remove_pmap m key == m, FS.remove key keys == keys,
    // the invariant should hold with the same cnt
    
    // Count stays the same
    fold (is_ht h (remove_pmap m key) (FS.remove key keys));
    false
  }
}

//////////////////////////////////////////////////////////////////////////////
// Size
//////////////////////////////////////////////////////////////////////////////

fn size
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
requires is_ht h m keys
returns n:SZ.t
ensures is_ht h m keys ** pure (SZ.v n == FS.cardinality keys)
{
  unfold (is_ht h m keys);
  with bucket_ptrs bucket_contents cnt. _;
  
  let n = B.op_Bang h.count;
  
  fold (is_ht h m keys);
  n
}

//////////////////////////////////////////////////////////////////////////////
// Free
//////////////////////////////////////////////////////////////////////////////

(** Free all buckets in on_range *)
fn rec free_all_buckets
  (#k:eqtype)
  (#v:Type0)
  (buckets:V.vec (bucket k v))
  (capacity:SZ.t{SZ.v capacity > 0})
  (i:SZ.t)
  (#bucket_ptrs:erased (Seq.seq (bucket k v)))
  (#bucket_contents:erased (Seq.seq (list (entry k v))))
requires 
  V.pts_to buckets bucket_ptrs **
  OR.on_range (bucket_at bucket_ptrs bucket_contents) (SZ.v i) (SZ.v capacity) **
  pure (Seq.length bucket_ptrs == SZ.v capacity /\ 
        Seq.length bucket_contents == SZ.v capacity /\
        SZ.v i <= SZ.v capacity)
ensures 
  V.pts_to buckets bucket_ptrs
decreases (SZ.v capacity - SZ.v i)
{
  if (i = capacity) {
    // No more buckets to free
    OR.on_range_empty_elim (bucket_at bucket_ptrs bucket_contents) (SZ.v capacity)
  } else {
    // Get the bucket at index i
    OR.on_range_uncons ();
    
    // Read the bucket pointer
    let b = V.op_Array_Access buckets i;
    
    // Unfold bucket_at
    unfold_bucket_at bucket_ptrs bucket_contents (SZ.v i);
    
    // Rewrite to use the concrete pointer
    rewrite (LL.is_list (Seq.index bucket_ptrs (SZ.v i)) (Seq.index bucket_contents (SZ.v i)))
         as (LL.is_list b (Seq.index bucket_contents (SZ.v i)));
    
    // Free the bucket
    free_bucket b;
    
    // Recurse
    let i_plus_1 = SZ.add i 1sz;
    free_all_buckets buckets capacity i_plus_1
  }
}

fn free
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
requires is_ht h m keys
ensures emp
{
  unfold (is_ht h m keys);
  with bucket_ptrs bucket_contents cnt. _;
  
  // Free all buckets
  free_all_buckets h.buckets h.capacity 0sz;
  
  // Free the vector
  V.free h.buckets;
  
  // Free the count box (now using Box which supports free!)
  B.free h.count;
  
  ()
}

//////////////////////////////////////////////////////////////////////////////
// Iterator Implementation
//////////////////////////////////////////////////////////////////////////////

(** Iterator type - stores current position using indices only *)
noeq
type ht_iter_t (k:eqtype) (v:Type0) = {
  it_ht: ht k v;                              // Reference to hash table
  it_bucket_idx: B.box SZ.t;                  // Current bucket index (0 to capacity)
  it_entry_idx: B.box SZ.t;                   // Current entry index within bucket
}

let ht_iter (k:eqtype) (v:Type0) = ht_iter_t k v

let ht_of (#k:eqtype) (#v:Type0) (it:ht_iter k v) : ht k v = it.it_ht

(** Get entries from position idx onwards in a list *)
let rec list_from_idx (#a:Type) (l:list a) (idx:nat) : list a =
  if idx = 0 then l
  else match l with
    | [] -> []
    | _::tl -> list_from_idx tl (idx - 1)

(** Build remaining keys from current position *)
let remaining_keys_from (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (bucket_idx:nat)
  (entry_idx:nat)
  : GTot (FS.set k) =
  if bucket_idx >= Seq.length bucket_contents then FS.emptyset
  else
    let current_bucket = Seq.index bucket_contents bucket_idx in
    let remaining_in_bucket = list_from_idx current_bucket entry_idx in
    FS.union (bucket_keys remaining_in_bucket) 
             (build_keys_from_buckets bucket_contents (bucket_idx + 1))

(** Predicate for iterator state *)
let is_ht_iter (#k:eqtype) (#v:Type0) (it:ht_iter k v) 
               (m:erased (pmap k v)) (all_keys:erased (FS.set k)) (remaining:erased (FS.set k)) : slprop =
  exists* (bucket_ptrs:Seq.seq (bucket k v)) 
          (bucket_contents:Seq.seq (list (entry k v))) 
          (cnt:SZ.t)
          (bucket_idx:SZ.t)
          (entry_idx:SZ.t).
    V.pts_to it.it_ht.buckets bucket_ptrs **
    B.pts_to it.it_ht.count cnt **
    B.pts_to it.it_bucket_idx bucket_idx **
    B.pts_to it.it_entry_idx entry_idx **
    OR.on_range (bucket_at bucket_ptrs bucket_contents) 0 (SZ.v it.it_ht.capacity) **
    pure (
      Seq.length bucket_ptrs == SZ.v it.it_ht.capacity /\
      Seq.length bucket_contents == SZ.v it.it_ht.capacity /\
      SZ.v cnt == total_count bucket_contents 0 /\
      all_buckets_wf bucket_contents it.it_ht.hashf (SZ.v it.it_ht.capacity) 0 /\
      all_buckets_no_dup bucket_contents 0 /\
      V.is_full_vec it.it_ht.buckets /\
      reveal m == build_pmap_from_buckets bucket_contents it.it_ht.hashf (SZ.v it.it_ht.capacity) 0 /\
      reveal all_keys == build_keys_from_buckets bucket_contents 0 /\
      SZ.v cnt == FS.cardinality (reveal all_keys) /\
      SZ.v bucket_idx <= SZ.v it.it_ht.capacity /\
      (SZ.v bucket_idx < SZ.v it.it_ht.capacity ==> 
         SZ.v entry_idx <= List.length (Seq.index bucket_contents (SZ.v bucket_idx))) /\
      reveal remaining == remaining_keys_from bucket_contents (SZ.v bucket_idx) (SZ.v entry_idx)
    )

//////////////////////////////////////////////////////////////////////////////
// Iterator Operations  
//////////////////////////////////////////////////////////////////////////////

(** Lemma: remaining_keys_from at capacity is empty *)
let remaining_keys_from_at_capacity (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  (entry_idx:nat)
  : Lemma 
    (ensures remaining_keys_from bucket_contents (Seq.length bucket_contents) entry_idx == FS.emptyset)
  = ()

(** Lemma: remaining_keys_from at 0,0 equals all keys *)
let remaining_keys_from_start (#k:eqtype) (#v:Type0)
  (bucket_contents:Seq.seq (list (entry k v)))
  : Lemma 
    (ensures remaining_keys_from bucket_contents 0 0 == build_keys_from_buckets bucket_contents 0)
  = FS.all_finite_set_facts_lemma ();
    if Seq.length bucket_contents = 0 then ()
    else ()  // list_from_idx l 0 = l, so remaining == build_keys

fn create_iter
  (#k:eqtype)
  (#v:Type0)
  (h:ht k v)
  (#m:erased (pmap k v))
  (#keys:erased (FS.set k))
requires is_ht h m keys
returns it:ht_iter k v
ensures is_ht_iter it m keys keys ** pure (ht_of it == h)
{
  unfold (is_ht h m keys);
  with bucket_ptrs bucket_contents cnt. _;
  
  // Allocate iterator state
  let bucket_idx_box = B.alloc 0sz;
  let entry_idx_box = B.alloc 0sz;
  
  // Create iterator record
  let it : ht_iter k v = {
    it_ht = h;
    it_bucket_idx = bucket_idx_box;
    it_entry_idx = entry_idx_box;
  };
  
  // Rewrite to use it.it_ht instead of h
  rewrite (V.pts_to h.buckets bucket_ptrs) as (V.pts_to it.it_ht.buckets bucket_ptrs);
  rewrite (B.pts_to h.count cnt) as (B.pts_to it.it_ht.count cnt);
  rewrite (OR.on_range (bucket_at bucket_ptrs bucket_contents) 0 (SZ.v h.capacity))
       as (OR.on_range (bucket_at bucket_ptrs bucket_contents) 0 (SZ.v it.it_ht.capacity));
  rewrite (B.pts_to bucket_idx_box 0sz) as (B.pts_to it.it_bucket_idx 0sz);
  rewrite (B.pts_to entry_idx_box 0sz) as (B.pts_to it.it_entry_idx 0sz);
  
  // Prove remaining_keys_from starts with all keys
  remaining_keys_from_start bucket_contents;
  
  fold (is_ht_iter it m keys keys);
  it
}

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
{
  admit()  // TODO: Need to check if bucket_idx < capacity or entry_idx < bucket length
}

fn iter_next
  (#k:eqtype)
  (#v:Type0)
  (it:ht_iter k v)
  (#m:erased (pmap k v))
  (#all_keys #remaining:erased (FS.set k))
requires is_ht_iter it m all_keys remaining ** pure (FS.cardinality remaining > 0)
returns p:(k & v)
ensures exists* remaining'.
        is_ht_iter it m all_keys remaining' **
        pure (
          FS.mem (fst p) remaining /\
          remaining' == FS.remove (fst p) remaining /\
          Some (snd p) == reveal m (fst p)
        )
{
  admit()  // TODO: Read current entry, advance indices
}

fn finish_iter
  (#k:eqtype)
  (#v:Type0)
  (it:ht_iter k v)
  (#m:erased (pmap k v))
  (#all_keys #remaining:erased (FS.set k))
requires is_ht_iter it m all_keys remaining
returns h:ht k v
ensures is_ht h m all_keys ** pure (h == ht_of it)
{
  unfold (is_ht_iter it m all_keys remaining);
  with bucket_ptrs bucket_contents cnt bucket_idx entry_idx. _;
  
  // Free iterator state boxes
  B.free it.it_bucket_idx;
  B.free it.it_entry_idx;
  
  fold (is_ht it.it_ht m all_keys);
  it.it_ht
}
