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
///   as a functional list, related by the lpts_to vprop

val lpts_to (#a:Type0) (ll:llist a) (l:list a) : vprop

/// Empty linked list is a value
val empty (a:Type0) : llist a

/// empty linked list points to empty list
val empty_pts_to (#opened:_) (a:Type0)
  : STGhostT unit opened
      emp
      (fun _ -> empty a `lpts_to` [])

/// The lpts_to assertion on empty linked list comes with an
///   inversion lemma
val empty_pts_to_inversion (#opened:_) (a:Type0) (l:list a)
  : STGhost unit opened
      (empty a `lpts_to` l)
      (fun _ -> empty a `lpts_to` l)
      (requires True)
      (ensures fun _ -> l == [])

/// Adding an element to the head of the linked list
inline_for_extraction
val cons (#a:Type0) (#l:G.erased (list a)) (x:a) (ll:llist a)
  : STT (llist a)
        (ll `lpts_to` l)
        (fun ll -> ll `lpts_to` (x::l))

/// Reading the head element of the linked list
inline_for_extraction
val peek (#a:Type0) (#l:G.erased (list a))
  (ll:llist a)
  (_:squash (Cons? l))
  : ST a
       (ll `lpts_to` l)
       (fun _ -> ll `lpts_to` l)
       (requires True)
       (ensures fun x -> x == Cons?.hd l)

/// Destructing the linked list
///   Returns the head element and the tail of the linked list
///   Frees up any resources associated with the (previous) head
inline_for_extraction
val destruct (#a:Type0) (#l:G.erased (list a))
  (ll:llist a)
  (_:squash (Cons? l))
  : ST (a & llist a)
       (ll `lpts_to` l)
       (fun (_, ll) -> ll `lpts_to` Cons?.tl l)
       (requires True)
       (ensures fun (x, _) -> x == Cons?.hd l)
