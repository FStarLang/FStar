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

   Author: Aseem Rastogi
*)

module LList.ST

open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util

open Steel.ST.Reference

module G = FStar.Ghost

/// This module provides a singly linked list in the
///   Steel sepearation logic framework


inline_for_extraction
noeq
type llist_node (a:Type0) : Type0 = {
  data : a;
  next : ref (llist_node a)
}


/// The main list type, parametric in the element type

inline_for_extraction
type llist (a:Type0) : Type0 = ref (llist_node a)


/// The module provides a logical view of the linked list
///   as a functional list, related by the is_list vprop

val is_list (#a:Type0) (ll:llist a) (l:list a) : vprop

/// Empty linked list is a value
val empty (a:Type0) : llist a

/// empty linked list points to empty list
val empty_pts_to (#opened:_) (a:Type0)
  : STGhostT unit opened
      emp
      (fun _ -> empty a `is_list` [])

/// The is_list assertion on empty linked list comes with an
///   inversion lemma
val empty_pts_to_inversion (#opened:_) (a:Type0) (l:list a)
  : STGhost unit opened
      (empty a `is_list` l)
      (fun _ -> empty a `is_list` l)
      (requires True)
      (ensures fun _ -> l == [])

/// Adding an element to the head of the linked list
inline_for_extraction
val cons (#a:Type0) (#l:G.erased (list a)) (x:a) (ll:llist a)
  : STT (llist a)
        (ll `is_list` l)
        (fun ll -> ll `is_list` (x::l))

/// Reading the head element of the linked list
inline_for_extraction
val peek (#a:Type0) (#l:G.erased (list a))
  (ll:llist a)
  (_:squash (Cons? l))
  : ST a
       (ll `is_list` l)
       (fun _ -> ll `is_list` l)
       (requires True)
       (ensures fun x -> x == Cons?.hd l)

val intro (#opened:_) (#a:Type0)
  (l:list a)
  (node:llist_node a)
  (ll:llist a)
  (_:squash (Cons? l))
  : STGhost unit opened
      (pts_to ll full_perm node
         `star`
       is_list node.next (Cons?.tl l))
      (fun _ -> is_list ll l)
      (requires node.data == Cons?.hd l)
      (ensures fun _ -> True)

val elim (#opened:_) (#a:Type0)
  (l:list a)
  (ll:llist a)
  (_:squash (Cons? l))
  : STGhost (llist_node a) opened
      (is_list ll l)
      (fun node ->
       pts_to ll full_perm node
         `star`
       is_list node.next (Cons?.tl l))
      (requires True)
      (ensures fun node -> node.data == Cons?.hd l)
