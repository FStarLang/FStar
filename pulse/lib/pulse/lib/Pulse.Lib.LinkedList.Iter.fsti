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

module Pulse.Lib.LinkedList.Iter

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LinkedList

/// Iterator type - abstract handle for iterating over a linked list
/// Stores both the current position and the original list head
val iter (t:Type0) : Type0

/// Pure function to get the original list pointer from an iterator
/// This is the pointer that was passed to create_iter
val llist_of (#t:Type0) (it:iter t) : llist t

/// Predicate for an iterator that borrows a linked list
/// - `it`: the iterator handle
/// - `original`: the full original list contents being iterated
/// - `remaining`: the suffix of the list that hasn't been visited yet
/// - Use `llist_of it` to reference the original pointer
val is_iter (#t:Type0) ([@@@mkey]it:iter t) 
            (original:erased (list t)) 
            (remaining:erased (list t))
  : Tot slprop

/// Create an iterator for a linked list
/// The iterator borrows the list (doesn't consume it)
/// Returns an iterator where llist_of it == x
fn create_iter (#t:Type0) (x:llist t)
  requires is_list x 'l
  returns it:iter t
  ensures is_iter it 'l 'l
  ensures pure (llist_of it == x)

/// Check if there are more elements to iterate
/// Returns true if remaining list is non-empty
fn has_next (#t:Type0) (it:iter t) 
            (#original #remaining: erased (list t))
  requires is_iter it original remaining
  returns b:bool
  ensures is_iter it original remaining ** 
          pure (b <==> Cons? remaining)

/// Get current element and advance to next
/// Requires that has_next returned true
/// Returns the head of remaining list and advances iterator to tail
fn next (#t:Type0) (it:iter t)
         (#original #remaining: erased (list t))
  requires is_iter it original remaining
  requires pure (Cons? remaining)
  returns v:t
  ensures exists* tl. 
          pure (remaining == v :: tl) **
          is_iter it original tl

/// Finish iteration and return the original list head
/// This "closes" the iterator and restores ownership of the original list
/// The returned pointer is exactly llist_of it
fn finish_iter (#t:Type0) (it:iter t)
               (#original: erased (list t))
  requires is_iter it original []
  returns x:llist t
  ensures is_list x original
  ensures pure (x == llist_of it)
